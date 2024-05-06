#![feature(try_blocks)]

enum FakeOption<T> {
    None,
    Some(T),
}

impl<T> FakeOption<T> {
    fn is_none(&self) -> bool {
        match self {
            Self::None => true,
            Self::Some(_) => false,
        }
    }
}

enum FakeResult<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> FakeResult<T, E> {
    fn is_err(&self) -> bool {
        match self {
            Self::Ok(_) => false,
            Self::Err(_) => true,
        }
    }
}
struct OptionOwner {
    owned: Option<String>, // `String` is not `Copy`
}
struct OptionOwnerOwner {
    owner: OptionOwner,
}

pub struct PatternedError {
    flag: bool,
}

fn do_something() {}

fn make_option() -> Option<u8> {
    None
}

fn make_result() -> Result<u8, u8> {
    Err(0)
}

// Input `Option`, return `None`
fn option_to_none() -> Option<u8> {
    let x = None;

    // `if let` returning `None` without semicolon
    let _ = if let Some(x) = x { x } else { return None };

    // `if let` returning `None` with semicolon (#11993)
    let _ = if let Some(x) = x {
        x
    } else {
        return None;
    };

    // `if let` returning the variable without semicolon
    // TODO: This currently does not trigger the lint
    let _ = if let Some(x) = x { x } else { return x };

    // `if let` returning the variable with semicolon (#11993)
    // TODO: This currently does not trigger the lint
    let _ = if let Some(x) = x {
        x
    } else {
        return x;
    };

    // `if let` against a function result
    let _ = if let Some(x) = make_option() {
        x
    } else {
        return None;
    };

    // `is_none` against a variable returning the variable
    // TODO: This currently does not trigger the lint
    if x.is_none() {
        return x;
    }

    // `is_none` against a variable returning `None`
    if x.is_none() {
        return None;
    }

    // `is_none` against a function result
    if make_option().is_none() {
        return None;
    }

    // Checking for `None` without unwrapping `Some`
    let _ = if x.is_none() {
        return None;
    } else {
        x
    };

    // `else if let`
    // TODO: This currently does not trigger the lint
    let _ = if true {
        1
    } else if let Some(x) = x {
        x
    } else {
        return None;
    };

    // `if let` completely inside a macro
    macro_rules! lint_inside_macro {
        ($x:ident) => {
            let _ = if let Some(x) = $x { x } else { return None };
        };
    }

    lint_inside_macro!(x);

    // `if let` against `Some` + comment before `return`
    // TODO: This currently triggers the lint
    let _ = if let Some(x) = x {
        x
    } else {
        // Please keep this comment
        return None;
    };

    // `is_none` + comment before `return`
    // TODO: This currently triggers the lint
    if x.is_none() {
        // Please keep this comment
        return None;
    }

    // `if let` against `Some` + other code before `return`
    let _ = if let Some(x) = x {
        x
    } else {
        do_something();
        return None;
    };

    // `is_none` + other code before `return`
    if x.is_none() {
        do_something();
        return None;
    }

    // `if let` against `Some` + other code in "then"
    let _ = if let Some(x) = x {
        do_something();
        x
    } else {
        return None;
    };

    // `is_none` + `else`
    if x.is_none() {
        return None;
    } else {
        do_something();
    }

    // Not `std::option::Option`
    {
        type Option<T> = FakeOption<T>;

        fn returns_fake_result() -> Option<u8> {
            let x = Option::None;
            let _ = if let Option::Some(x) = x { x } else { return x };
            Option::Some(0)
        }
    }

    // See #8628, #12337, #11001
    fn try_blocks() {
        // `x?` is not the same as `return None` inside of a try block
        fn nested(x: Option<u8>) -> Option<u8> {
            let b: Option<u8> = try {
                let _ = if let Some(x) = x { x } else { return None };
                0
            };
            b.or(Some(1))
        }

        // `fn` inside `try`
        fn fn_in_try() -> Option<u32> {
            try {
                fn nested(x: Option<i32>) -> Option<i32> {
                    // Do lint, the outer `try` is not relevant here
                    if x.is_none() {
                        return None;
                    }
                    Some(0)
                }
                0
            }
        }
    }

    // `?` cannot be used in const context (#9175)
    const fn in_const(x: Option<u8>) -> Option<u8> {
        let _ = if let Some(x) = x { x } else { return None };
        Some(0)
    }

    // `&Option` does not impl `Try` (#11983)
    let opt_ref = &x;
    let Some(y) = opt_ref else { return None };

    // `Try::branch` takes ownership of `x` in `x?`, and `(&x)?` also doesn't work since it's `&Option`
    // (#11983)
    let Some(y) = &x else { return None };
    let mov = x;

    fn issue12412(owner: &OptionOwner, owner_owner: &OptionOwnerOwner) -> Option<u8> {
        // Don't lint, `owned` is behind a shared reference
        let Some(_) = &owner.owned else {
            return None;
        };
        // Don't lint, `owned` is behind a shared reference
        let Some(_) = &owner_owner.owner.owned else {
            return None;
        };
        // Lint
        let Some(_) = owner_owner.owner.owned.clone() else {
            return None;
        };
        Some(0)
    }

    fn as_ref_with_shared_ref(x: &(Option<String>,)) -> Option<String> {
        // `Try::branch` takes `self`, hence `x.0?` would consume `x.0` (because `Option<String>` is not
        // `Copy`). We cannot do that, because we only have a shared ref. But we can use `x.0.as_ref()?`, so
        // that `branch` gets an `Option<&String>` instead, which is `Copy`.
        if x.0.is_none() {
            return None;
        }
        None
    }

    fn as_ref_with_later_use(opt: Option<String>) -> Option<String> {
        // In principal we could consume `opt` here, however it is used afterwards. Again, `as_ref` is the
        // solution.
        if opt.is_none() {
            return None;
        }
        opt
    }

    fn ref_pattern(opt: Option<String>) -> Option<String> {
        // Since we extract using `ref` here the fixed expression should also return a reference. We can
        // accomplish that using `as_ref`.
        let s: &String = if let Some(ref s) = opt {
            s
        } else {
            return None;
        };
        None
    }

    // `question_mark_used` is active (#11283)
    #[warn(clippy::question_mark_used)]
    {
        let _ = if let Some(x) = x { x } else { return None };
    }

    // Refutable pattern
    let tuple_option = Some((1, 1));
    let _ = if let Some((1, y)) = tuple_option {
        (1, y)
    } else {
        return None;
    };

    // `if let` against `Some` across a macro boundary
    macro_rules! some {
        ($x:ident) => {
            Some($x)
        };
    }
    let _ = if let some!(x) = x {
        x
    } else {
        return None;
    };

    // `is_none` across a macro boundary
    macro_rules! is_none {
        ($x:ident) => {
            $x.is_none()
        };
    }
    // TODO: This currently gets "fixed" to `$x?;` (including the `$`)
    /*
    if is_none!(x) {
        return None;
    }
    */

    Some(0)
}

// Input `Result`, return `Err` unchanged
fn result_to_unchanged_err() -> Result<u8, u8> {
    let x = Err(0);

    // `if let` against `Ok` using a variable without semicolon
    let _ = if let Ok(x) = x { x } else { return x };

    // `if let` against `Ok` using a variable with semicolon (#11993)
    let _ = if let Ok(x) = x {
        x
    } else {
        return x;
    };

    // `if let` against `Ok` using a function result
    // TODO: This currently does not trigger the lint
    let _ = if let Ok(x) = make_result() { x } else { return x };

    // `if let` against `Err` using destructured variable
    if let Err(e) = x {
        return Err(e);
    }

    // `if let` against `Err` using original variable
    if let Err(y) = x {
        return x;
    }

    // `if let` against `Err` using a function result
    if let Err(x) = make_result() {
        return Err(x);
    };

    // Simple `is_err`
    if x.is_err() {
        return x;
    }

    // Checking for `Err` without unwrapping `Ok`
    let _ = if x.is_err() {
        return x;
    } else {
        x
    };

    // `else if let`  against `Ok`
    // TODO: This currently does not trigger the lint
    let _ = if true {
        1
    } else if let Ok(x) = x {
        x
    } else {
        return x;
    };

    // `else if let`  against `Err`
    // TODO: This currently does not trigger the lint
    let _ = if true {
        Ok(1)
    } else if let Err(x) = x {
        return Err(x);
    } else {
        x
    };

    // `if let` completely inside a macro
    macro_rules! lint_inside_macro {
        ($x:ident) => {
            let _ = if let Ok(x) = $x { x } else { return $x };
        };
    }

    lint_inside_macro!(x);

    // `if let` against `Ok`` + custom error
    let _ = if let Ok(x) = x {
        x
    } else {
        return Err(1);
    };

    // `if let` against `Err` + custom error
    if let Err(e) = x {
        return Err(1);
    }

    // `is_err` + custom error
    if x.is_err() {
        return Err(1);
    }

    // `if let` against `Ok` + comment before `return`
    // TODO: This currently triggers the lint
    let _ = if let Ok(x) = x {
        x
    } else {
        // Please keep this comment
        return x;
    };

    // `if let` against `Err` using destructured variable + comment before `return`
    // TODO: This currently triggers the lint
    if let Err(e) = x {
        // Please keep this comment
        return Err(e);
    }

    // `if let` against `Err` using original variable + comment before `return`
    // TODO: This currently triggers the lint
    if let Err(y) = x {
        // Please keep this comment
        return x;
    }

    // `is_err` + comment before `return`
    if x.is_err() {
        // Please keep this comment
        return Err(1);
    }

    // `if let` against `Ok` + other code before `return`
    let _ = if let Ok(x) = x {
        x
    } else {
        do_something();
        return x;
    };

    // `if let` against `Err` using destructured variable + other code before `return`
    if let Err(e) = x {
        do_something();
        return Err(e);
    }

    // `if let` against `Err` using original variable + other code before `return`
    if let Err(y) = x {
        do_something();
        return x;
    }

    // `is_err` + other code before `return`
    if x.is_err() {
        do_something();
        return x;
    }

    // `if let` against `Ok` + other code in "then"
    // TODO: This currently triggers the lint
    let _ = if let Ok(x) = x {
        do_something();
        x
    } else {
        return x;
    };

    // `if let` against `Err` + `else`
    if let Err(e) = x {
        return Err(e);
    } else {
        do_something();
    }

    // `is_err` + `else`
    if x.is_err() {
        return x;
    } else {
        do_something();
    }

    // `Ok` is returned
    let _ = if let Err(e) = x { x } else { return x };

    // Not `std::result::Result` (#8019)
    {
        type Result<T, E> = FakeResult<T, E>;

        fn returns_fake_result() -> Result<u8, u8> {
            let x = Result::Err(0);
            let _ = if let Result::Ok(x) = x { x } else { return x };

            Result::Ok(0)
        }
    }

    // See #8628, #12337, #11001
    fn try_blocks() {
        // `x?` is not the same as `return x` inside of a try block
        fn nested(x: Result<u8, u8>) -> Result<u8, u8> {
            let b: Result<u8, u8> = try {
                let _ = if let Ok(x) = x { x } else { return x };
                0
            };
            b.or(Ok(1))
        }

        // `fn` inside `try`
        fn fn_in_try() -> Result<u8, u8> {
            try {
                fn nested(x: Result<u8, u8>) -> Result<u8, u8> {
                    // Do lint, the outer `try` is not relevant here
                    if x.is_err() {
                        return x;
                    }
                    Ok(0)
                }
                0
            }
        }
    }

    // `?` cannot be used in const context (#9175)
    const fn in_const(x: Result<u8, u8>) -> Result<u8, u8> {
        let _ = if let Ok(x) = x { x } else { return x };
        Ok(0)
    }

    fn as_ref_with_later_use(res: Result<String, String>) -> Result<String, String> {
        // In principal we could consume `res` here, however it is used afterwards. Using `as_ref` is the
        // solution.
        if res.is_err() {
            return res;
        }
        res
    }

    fn ref_pattern(res: Result<String, String>) -> Result<String, String> {
        // Since we extract using `ref` here the fixed expression should also return a reference. We can
        // accomplish that using `as_ref`.
        let s: &String = if let Ok(ref s) = res {
            s
        } else {
            return res;
        };
        Ok("foo".into())
    }

    // `question_mark_used` is active (#11283)
    #[warn(clippy::question_mark_used)]
    {
        let _ = if let Ok(x) = x { x } else { return x };
    }

    // Refutable patterns
    fn refutable_patterns() -> Result<u8, PatternedError> {
        let res = Ok(0);
        if let Err(PatternedError { flag: true }) = res {
            return res;
        }
        if let Err(err @ PatternedError { flag: true }) = res {
            return Err(err);
        }
        let _ = if let Ok(1) = res { 1 } else { return res };
        res
    }

    // `if let` against `Ok` across a macro boundary
    macro_rules! ok {
        ($x:ident) => {
            Ok($x)
        };
    }
    let _ = if let ok!(x) = x {
        x
    } else {
        return x;
    };

    // `if let` against `Err` across a macro boundary
    macro_rules! err {
        ($x:ident) => {
            Err($x)
        };
    }
    if let err!(x) = x {
        return Err(x);
    };

    // `is_err` across a macro boundary
    macro_rules! is_err {
        ($x:ident) => {
            $x.is_err()
        };
    }
    // TODO: This currently gets "fixed" to `$x?;` (including the `$`)
    /*
    if is_err!(x) {
        return x;
    }
    */

    Ok(0)
}

fn main() {}
