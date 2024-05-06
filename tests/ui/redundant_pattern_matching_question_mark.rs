#![feature(try_blocks)]

// Interaction between `redundant_pattern_matching` and `question_mark`. If both are active,
// `question_mark` should take precedence where possible, since it results in shorter and more
// idiomatic code.

fn do_something() {}

// Input `Option`, return `None`
fn option_to_none() -> Option<u8> {
    let x = None;

    // `if let` against `None` returning the variable, should use `?'`
    // TODO: Currently is fixed to use `is_none`
    if let None = x {
        return x;
    };

    // Same, but with `question_mark` disabled, should use `is_none`
    #[allow(clippy::question_mark)]
    if let None = x {
        return x;
    };

    // `if let` against `None` returning `None`, should use `?`
    // TODO: Currently gets fixed as `if x.is_none() { return None }`, which triggers `question_mark`
    /*
    if let None = x {
        return None;
    };
    */

    // Same, but with `question_mark` disabled, should use `is_none`
    #[allow(clippy::question_mark)]
    if let None = x {
        return None;
    };

    // `else if let`, should use `?`
    // TODO: Currently is fixed to use `is_none`
    let _ = if true {
        Some(1)
    } else if let None = x {
        return None;
    } else {
        x
    };

    // Same, but with `question_mark` disabled, should use `is_none`
    #[allow(clippy::question_mark)]
    let _ = if true {
        Some(1)
    } else if let None = x {
        return None;
    } else {
        x
    };

    // `if let` against `None` where `question_mark` doesn't trigger, should use `is_none`
    if let None = x {
        do_something();
    }

    Some(0)
}

// Input `Result`, return `Err` unchanged
fn result_to_unchanged_err() -> Result<u8, u8> {
    let x = Err(0);

    // `if let` against `Err` returning the variable, should use `?`
    // TODO: Currently gets fixed as `if x.is_err() { return x }`, which triggers `question_mark`
    /*
    if let Err(_) = x {
        return x;
    }
    */

    // Same, but with `question_mark` disabled, should use `is_err`
    #[allow(clippy::question_mark)]
    if let Err(_) = x {
        return x;
    }

    // `else if let`, should use `?`
    // TODO: Currently is fixed to use `is_err`
    let _ = if true {
        Ok(1)
    } else if let Err(_) = x {
        return x;
    } else {
        x
    };

    // Same, but with `question_mark` disabled, should use `is_err`
    #[allow(clippy::question_mark)]
    let _ = if true {
        Ok(1)
    } else if let Err(_) = x {
        return x;
    } else {
        x
    };

    // `if let` against `Err` where `question_mark` doesn't trigger, should use `is_err`
    if let Err(_) = x {
        do_something();
    }

    Ok(0)
}

fn main() {}
