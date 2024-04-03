use crate::manual_let_else::MANUAL_LET_ELSE;
use crate::question_mark_used::QUESTION_MARK_USED;
use clippy_config::msrvs::Msrv;
use clippy_config::types::MatchLintBehaviour;

use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::source::snippet_with_applicability;
use clippy_utils::ty::{implements_trait, is_type_diagnostic_item};
use clippy_utils::{
    can_if_let_and_early_return_be_question_mark, eq_expr_value, extract_var, higher, in_constant, is_else_clause,
    is_lint_allowed, is_path_lang_item, is_refutable, path_to_local, peel_blocks, OptionOrResult, QuestionMarkBlock,
    QuestionMarkBlockValue,
};
use rustc_ast::BindingAnnotation;
use rustc_errors::Applicability;

use rustc_hir::LangItem::{self};
use rustc_hir::{ByRef, Expr, ExprKind, Local, Node, PatKind, Stmt, StmtKind};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;
use rustc_span::sym;

declare_clippy_lint! {
    /// ### What it does
    /// Checks for expressions that could be replaced by the question mark operator.
    ///
    /// ### Why is this bad?
    /// Question mark usage is more idiomatic.
    ///
    /// ### Example
    /// ```ignore
    /// if option.is_none() {
    ///     return None;
    /// }
    /// ```
    ///
    /// Could be written:
    ///
    /// ```ignore
    /// option?;
    /// ```
    #[clippy::version = "pre 1.29.0"]
    pub QUESTION_MARK,
    style,
    "checks for expressions that could be replaced by the question mark operator"
}

pub struct QuestionMark {
    pub(crate) msrv: Msrv,
    pub(crate) matches_behaviour: MatchLintBehaviour,
    /// Keeps track of how many try blocks we are in at any point during linting.
    /// This allows us to answer the question "are we inside of a try block"
    /// very quickly, without having to walk up the parent chain, by simply checking
    /// if it is greater than zero.
    /// As for why we need this in the first place: <https://github.com/rust-lang/rust-clippy/issues/8628>
    try_block_depth_stack: Vec<u32>,
}

impl_lint_pass!(QuestionMark => [QUESTION_MARK, MANUAL_LET_ELSE]);

impl QuestionMark {
    #[must_use]
    pub fn new(msrv: Msrv, matches_behaviour: MatchLintBehaviour) -> Self {
        Self {
            msrv,
            matches_behaviour,
            try_block_depth_stack: Vec::new(),
        }
    }

    fn inside_try_block(&self) -> bool {
        self.try_block_depth_stack.last() > Some(&0)
    }
}

/// Checks if the given expression on the given context matches the following structure:
///
/// ```ignore
/// if option.is_none() {
///    return None;
/// }
/// ```
///
/// ```ignore
/// if result.is_err() {
///     return result;
/// }
/// ```
///
/// If it matches, it will suggest to use the question mark operator instead.
fn check_is_none_or_err_and_early_return<'tcx>(cx: &LateContext<'tcx>, expr: &Expr<'tcx>) {
    if let Some(higher::If { cond, then, r#else }) = higher::If::hir(expr)
        && !is_else_clause(cx.tcx, expr)
        && let ExprKind::MethodCall(segment, caller, ..) = &cond.kind
        && let caller_ty = cx.typeck_results().expr_ty(caller)
        && let Some(QuestionMarkBlock {
            value,
            has_return: true,
            ..
        }) = QuestionMarkBlock::from_expr(cx, then)
        && match value {
            QuestionMarkBlockValue::None => {
                is_type_diagnostic_item(cx, caller_ty, sym::Option) && segment.ident.name == sym!(is_none)
            },
            QuestionMarkBlockValue::Var(hir_id) => {
                is_type_diagnostic_item(cx, caller_ty, sym::Result)
                    && segment.ident.name == sym!(is_err)
                    && path_to_local(caller) == Some(hir_id)
            },
            // TODO: We could suggest `result.map_err(..)?` here
            QuestionMarkBlockValue::Err(_) => false,
        }
    {
        let mut applicability = Applicability::MachineApplicable;
        let receiver_str = snippet_with_applicability(cx, caller.span, "..", &mut applicability);
        let by_ref = !caller_ty.is_copy_modulo_regions(cx.tcx, cx.param_env)
            && !matches!(caller.kind, ExprKind::Call(..) | ExprKind::MethodCall(..));
        let sugg = if let Some(else_inner) = r#else {
            if eq_expr_value(cx, caller, peel_blocks(else_inner)) {
                format!("Some({receiver_str}?)")
            } else {
                return;
            }
        } else {
            format!("{receiver_str}{}?;", if by_ref { ".as_ref()" } else { "" })
        };

        span_lint_and_sugg(
            cx,
            QUESTION_MARK,
            expr.span,
            "this block may be rewritten with the `?` operator",
            "replace it with",
            sugg,
            applicability,
        );
    }
}

/// Checks for patterns like
///
/// ```ignore
/// if let Some(y) = g() { y } else { return None };
/// ```
/// (suggests `g()?;`)
///
/// ```ignore
/// if let Some(y) = z { y } else { return z };
/// ```
/// (suggests `z?`)
///
/// ```ignore
/// if let Ok(y) = z { y } else { return z };
/// ```
/// (suggests `z?`)
///
/// ```ignore
/// if let Err(e) = h() { return Err(e) };
/// ```
/// (suggests `h()?`)
fn check_if_let_and_early_return<'tcx>(cx: &LateContext<'tcx>, expr: &Expr<'tcx>) {
    if can_if_let_and_early_return_be_question_mark(cx, expr)
        && let Some(higher::IfLet { let_pat, let_expr, .. }) = higher::IfLet::hir(cx, expr)
        && let PatKind::TupleStruct(_, [field], _) = let_pat.kind
        && let PatKind::Binding(BindingAnnotation(by_ref, _), ..) = field.kind
    {
        let mut applicability = Applicability::MachineApplicable;
        let receiver_str = snippet_with_applicability(cx, let_expr.span, "..", &mut applicability);
        let requires_semi = matches!(cx.tcx.parent_hir_node(expr.hir_id), Node::Stmt(_));
        let sugg = format!(
            "{receiver_str}{}?{}",
            if by_ref == ByRef::Yes { ".as_ref()" } else { "" },
            if requires_semi { ";" } else { "" }
        );
        span_lint_and_sugg(
            cx,
            QUESTION_MARK,
            expr.span,
            "this block may be rewritten with the `?` operator",
            "replace it with",
            sugg,
            applicability,
        );
    }
}

/// Check `let .. else { return .. }` statements
///
/// ```ignore
/// let Some(y) = g() else { return None };
/// ```
/// (suggests `let y = g()?;`)
///
/// ```ignore
/// let Some(y) = z else { return z };
/// ```
/// (suggests `let y = z?;`)
///
/// ```ignore
/// let Ok(y) = z else { return z };
/// ```
/// (suggests `let y = z?`;)
fn check_let_else_and_early_return<'tcx>(cx: &LateContext<'tcx>, stmt: &Stmt<'tcx>) {
    /// Make sure the init expr implements try trait so a valid suggestion could be given.
    ///
    /// Because the init expr could have the type of `&Option<T>` which does not implements
    /// `Try`.
    ///
    /// NB: This conveniently prevents the cause of
    /// issue [#12412](https://github.com/rust-lang/rust-clippy/issues/12412),
    /// since accessing an `Option` field from a borrowed struct requires borrow, such as
    /// `&some_struct.opt`, which is type of `&Option`. And we can't suggest `&some_struct.opt?`
    /// or `(&some_struct.opt)?` since the first one has different semantics and the later does
    /// not implements `Try`.
    fn init_expr_can_use_question_mark(cx: &LateContext<'_>, init_expr: &Expr<'_>) -> bool {
        let init_ty = cx.typeck_results().expr_ty_adjusted(init_expr);
        cx.tcx
            .lang_items()
            .try_trait()
            .map_or(false, |did| implements_trait(cx, init_ty, did, &[]))
    }

    if let StmtKind::Let(Local {
        pat,
        init: Some(init_expr),
        els: Some(els),
        ..
    }) = stmt.kind
        && init_expr_can_use_question_mark(cx, init_expr)
        && let PatKind::TupleStruct(ref path, [field], ddpos) = pat.kind
        && !is_refutable(cx, field)
        && ddpos.as_opt_usize().is_none()
        && let Some(else_block) = QuestionMarkBlock::from_block(cx, els)
        && else_block.has_return
        // If the `else`` block returns a variable it must be the same as the one the pattern is compared to
        && {
            match else_block.value {
                QuestionMarkBlockValue::Var(return_var) => extract_var(init_expr) == Some(return_var),
                _ => true,
            }
        }
        && let Some(input_type) = OptionOrResult::from_some_or_ok(cx, cx.qpath_res(path, pat.hir_id))
        && else_block.can_be_shortened(input_type)
    {
        let mut applicability = Applicability::MachineApplicable;
        let init_expr_str = snippet_with_applicability(cx, init_expr.span, "..", &mut applicability);
        let receiver_str = snippet_with_applicability(cx, field.span, "..", &mut applicability);
        let sugg = format!("let {receiver_str} = {init_expr_str}?;");

        span_lint_and_sugg(
            cx,
            QUESTION_MARK,
            stmt.span,
            "this `let...else` may be rewritten with the `?` operator",
            "replace it with",
            sugg,
            applicability,
        );
    }
}

fn is_try_block(cx: &LateContext<'_>, bl: &rustc_hir::Block<'_>) -> bool {
    if let Some(expr) = bl.expr
        && let ExprKind::Call(callee, _) = expr.kind
    {
        is_path_lang_item(cx, callee, LangItem::TryTraitFromOutput)
    } else {
        false
    }
}

impl<'tcx> LateLintPass<'tcx> for QuestionMark {
    fn check_stmt(&mut self, cx: &LateContext<'tcx>, stmt: &'tcx Stmt<'_>) {
        if !is_lint_allowed(cx, QUESTION_MARK_USED, stmt.hir_id) {
            return;
        }

        if !self.inside_try_block() && !in_constant(cx, stmt.hir_id) {
            check_let_else_and_early_return(cx, stmt);
        }
        self.check_manual_let_else(cx, stmt);
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        if !self.inside_try_block()
            && !in_constant(cx, expr.hir_id)
            && is_lint_allowed(cx, QUESTION_MARK_USED, expr.hir_id)
        {
            check_is_none_or_err_and_early_return(cx, expr);
            check_if_let_and_early_return(cx, expr);
        }
    }

    fn check_block(&mut self, cx: &LateContext<'tcx>, block: &'tcx rustc_hir::Block<'tcx>) {
        if is_try_block(cx, block) {
            *self
                .try_block_depth_stack
                .last_mut()
                .expect("blocks are always part of bodies and must have a depth") += 1;
        }
    }

    fn check_body(&mut self, _: &LateContext<'tcx>, _: &'tcx rustc_hir::Body<'tcx>) {
        self.try_block_depth_stack.push(0);
    }

    fn check_body_post(&mut self, _: &LateContext<'tcx>, _: &'tcx rustc_hir::Body<'tcx>) {
        self.try_block_depth_stack.pop();
    }

    fn check_block_post(&mut self, cx: &LateContext<'tcx>, block: &'tcx rustc_hir::Block<'tcx>) {
        if is_try_block(cx, block) {
            *self
                .try_block_depth_stack
                .last_mut()
                .expect("blocks are always part of bodies and must have a depth") -= 1;
        }
    }
    extract_msrv_attr!(LateContext);
}
