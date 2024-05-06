use crate::manual_let_else::MANUAL_LET_ELSE;
use crate::question_mark_used::QUESTION_MARK_USED;
use clippy_config::msrvs::Msrv;
use clippy_config::types::MatchLintBehaviour;

use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::source::snippet_with_applicability;
use clippy_utils::ty::{implements_trait, is_type_diagnostic_item};
use clippy_utils::{
    eq_expr_value, extract_var, higher, in_constant, is_else_clause, is_lint_allowed, is_path_lang_item, is_refutable,
    is_res_lang_ctor, path_to_local, path_to_local_id, peel_blocks, OptionOrResult, QuestionMarkBlock,
    QuestionMarkBlockSuggestion, QuestionMarkBlockValue,
};
use rustc_ast::BindingMode;
use rustc_errors::Applicability;

use rustc_hir::LangItem::{self, ResultErr};
use rustc_hir::{ByRef, Expr, ExprKind, LetStmt, Node, PatKind, Stmt, StmtKind};
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

/// Check if the result of an expression implements `Try`.
///
/// NB: This conveniently prevents the cause of
/// issue [#12412](https://github.com/rust-lang/rust-clippy/issues/12412),
/// since accessing an `Option` field from a borrowed struct requires borrow, such as
/// `&some_struct.opt`, which is type of `&Option`. And we can't suggest `&some_struct.opt?`
/// or `(&some_struct.opt)?` since the first one has different semantics and the later does
/// not implements `Try`.
fn implements_try(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ty = cx.typeck_results().expr_ty_adjusted(expr);
    cx.tcx
        .lang_items()
        .try_trait()
        .map_or(false, |did| implements_trait(cx, ty, did, &[]))
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
}

impl QuestionMark {
    fn inside_try_block(&self) -> bool {
        self.try_block_depth_stack.last() > Some(&0)
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
    /// if option.is_none() {
    ///    return option;
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
    fn check_is_none_or_err_and_early_return<'tcx>(&self, cx: &LateContext<'tcx>, expr: &Expr<'tcx>) {
        if !self.inside_try_block()
            && let Some(higher::If { cond, then, r#else }) = higher::If::hir(expr)
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
                    (is_type_diagnostic_item(cx, caller_ty, sym::Result) && segment.ident.name == sym!(is_err))
                        || (is_type_diagnostic_item(cx, caller_ty, sym::Option) && segment.ident.name == sym!(is_none))
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
    /// if let Some(y) = g() { y } else { return Err(..) };
    /// ```
    /// (suggests `g().ok_or(...)?` or `g().ok_or_else(|| ..)?`)
    ///
    /// ```ignore
    /// if let Ok(y) = h() { y } else { return None };
    /// ```
    /// (suggests `h().ok()?`)
    ///
    /// ```ignore
    /// if let Ok(y) = z { y } else { return z };
    /// ```
    /// (suggests `z?`)
    ///
    /// ```ignore
    /// if let Ok(y) = h() { y } else { return Err(..) };
    /// ```
    /// (suggests `h().or(Err(..))?` or `h().map_err(|| ..)?`)
    ///
    /// ```ignore
    /// if let Err(e) = h() { return Err(e) };
    /// ```
    /// (suggests `h()?`)
    fn check_if_let_and_early_return<'tcx>(&self, cx: &LateContext<'tcx>, expr: &Expr<'tcx>) {
        if !self.inside_try_block()
            && let Some(higher::IfLet {
                let_pat,
                let_expr,
                if_then,
                if_else,
                ..
            }) = higher::IfLet::hir(cx, expr)
            && implements_try(cx, let_expr)
            && !is_else_clause(cx.tcx, expr)
            && let PatKind::TupleStruct(ref path1, [field], ddpos) = let_pat.kind
            && !is_refutable(cx, field)
            && ddpos.as_opt_usize().is_none()
            && let PatKind::Binding(BindingMode(by_ref, _), bind_id, _, None) = field.kind
        {
            let mut applicability = Applicability::MachineApplicable;
            let res = cx.qpath_res(path1, let_pat.hir_id);
            let msg;
            let call;

            if if_else.is_none() {
                // No `else` block

                // Check if the pattern is `Err(..)`
                if is_res_lang_ctor(cx, res, ResultErr)
                    && let Some(QuestionMarkBlock {
                        value: block_value,
                        has_return: true,
                        ..
                    }) = QuestionMarkBlock::from_expr(cx, if_then)
                    && match block_value {
                        // Either return `Err(x)` where `x` is the same variable as inside the `Err` pattern
                        QuestionMarkBlockValue::Err(err_arg) => extract_var(err_arg) == Some(bind_id),
                        // Or, if we matched against a variable, return that
                        QuestionMarkBlockValue::Var(var_id) => extract_var(let_expr) == Some(var_id),
                        _ => false,
                    }
                {
                    msg = "this block may be rewritten with the `?` operator".to_owned();
                    call = String::new();
                } else {
                    return;
                }
            } else {
                // There is an `else` block

                // Check if the argument to `Some`/`Ok` matches the expression in the "then" block
                if path_to_local_id(peel_blocks(if_then), bind_id)
                    && let Some(else_block) = QuestionMarkBlock::from_expr(cx, if_else.unwrap())
                    && else_block.has_return
                    // If the `else`` block returns a variable it must be the same as the one the pattern is compared to
                    && {
                        match else_block.value {
                            QuestionMarkBlockValue::Var(return_var) => extract_var(let_expr) == Some(return_var),
                            _ => true,
                        }
                    }
                {
                    let Some(input_type) = OptionOrResult::from_some_or_ok(cx, res) else {
                        return;
                    };
                    match else_block.prepare_suggestion(input_type, &mut applicability) {
                        Some(QuestionMarkBlockSuggestion::QuestionMarkOnly) => {
                            msg = "this block may be rewritten with the `?` operator".to_owned();
                            call = String::new();
                        },
                        Some(QuestionMarkBlockSuggestion::MethodCall(method_name, call_)) => {
                            msg = format!("this block may be rewritten with `{method_name}` and the `?` operator");
                            call = call_;
                        },
                        None => return,
                    };
                } else {
                    return;
                }
            }
            let receiver_str = snippet_with_applicability(cx, let_expr.span, "..", &mut applicability);
            let requires_semi = matches!(cx.tcx.parent_hir_node(expr.hir_id), Node::Stmt(_));
            let sugg = format!(
                "{receiver_str}{}{call}?{}",
                if matches!(by_ref, ByRef::Yes(_)) {
                    ".as_ref()"
                } else {
                    ""
                },
                if requires_semi { ";" } else { "" }
            );
            span_lint_and_sugg(
                cx,
                QUESTION_MARK,
                expr.span,
                msg,
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
    /// let Some(y) = g() else { return Err(x) };
    /// ```
    /// (suggests `let y = g().ok_or(..)?;` if `x` is const)
    ///
    /// ```ignore
    /// let Ok(y) = h() else { return None };
    /// ```
    /// (suggests `let y = h().ok()?;`)
    ///
    /// ```ignore
    /// let Ok(y) = h() else { return Err(x) };
    /// ```
    /// (suggests `let y = h().or(Err(..))?;` if `x` is const)
    ///
    /// ```ignore
    /// let Ok(y) = z else { return z };
    /// ```
    /// (suggests `let y = z?`;)
    fn check_let_else_and_early_return<'tcx>(cx: &LateContext<'tcx>, stmt: &Stmt<'tcx>) {
        if let StmtKind::Let(LetStmt {
            pat,
            init: Some(init_expr),
            els: Some(els),
            ..
        }) = stmt.kind
            && implements_try(cx, init_expr)
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
        {
            let Some(input_type) = OptionOrResult::from_some_or_ok(cx, cx.qpath_res(path, pat.hir_id)) else {
                return;
            };
            let mut applicability = Applicability::MachineApplicable;
            let msg;
            let call;
            match else_block.prepare_suggestion(input_type, &mut applicability) {
                Some(QuestionMarkBlockSuggestion::QuestionMarkOnly) => {
                    msg = "this `let...else` may be rewritten with the `?` operator".to_owned();
                    call = String::new();
                },
                Some(QuestionMarkBlockSuggestion::MethodCall(method_name, call_)) => {
                    msg = format!("this `let...else` may be rewritten with `{method_name}` and the `?` operator");
                    call = call_;
                },
                None => return,
            };
            let init_expr_str = snippet_with_applicability(cx, init_expr.span, "..", &mut applicability);
            let receiver_str = snippet_with_applicability(cx, field.span, "..", &mut applicability);
            let sugg = format!("let {receiver_str} = {init_expr_str}{call}?;");

            span_lint_and_sugg(
                cx,
                QUESTION_MARK,
                stmt.span,
                msg,
                "replace it with",
                sugg,
                applicability,
            );
        }
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
        if is_lint_allowed(cx, QUESTION_MARK_USED, stmt.hir_id) {
            if !in_constant(cx, stmt.hir_id) {
                QuestionMark::check_let_else_and_early_return(cx, stmt);
            }
            self.check_manual_let_else(cx, stmt);
        }
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        if !in_constant(cx, expr.hir_id) && is_lint_allowed(cx, QUESTION_MARK_USED, expr.hir_id) {
            self.check_is_none_or_err_and_early_return(cx, expr);
            self.check_if_let_and_early_return(cx, expr);
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
