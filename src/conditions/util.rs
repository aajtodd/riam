/// Test whether the context values are a subset of the condition values.
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn is_subset<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
{
    'outer: for ctxv in ctx_values.iter() {
        // every value in the context has to be a member of the condition values
        for condv in cond_values.iter() {
            if cmp(condv, ctxv) {
                continue 'outer;
            }
        }

        // no condv matched
        return false;
    }
    true
}

/// Test whether there is an intersection between the context values and the condition values
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn intersects<'a, T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
{
    for ctxv in ctx_values.iter() {
        for condv in cond_values.iter() {
            if cmp(condv, ctxv) {
                return true;
            }
        }
    }
    false
}

/// test whether all of the context values are not equal to any of the condition values, equivalent
/// to testing for the empty intersection.
/// The comparison function F will be invoked as F(condv, ctxv)
pub fn is_disjoint<T, F>(cond_values: &[T], ctx_values: &[T], cmp: F) -> bool
where
    F: Fn(&T, &T) -> bool,
    T: ::std::fmt::Debug,
{
    !intersects(cond_values, ctx_values, cmp)
}
