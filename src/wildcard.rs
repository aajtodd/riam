/// Test whether the incoming pattern string 's' matches the given pattern string 'pattern'.
///
/// A wildcard '*' character may appear anywhere in the `pattern`. A wildcard character matches
/// any character any number of times until the next character in the pattern is seen. If the
/// wildcard is the last char in the pattern then the remaining input string must be a match.
///
/// e.g. `abc*xyz` matches `abcdefghijkxyz`
///
/// If no wildcard is present in the pattern the inputs must be an exact match.
///
pub(crate) fn matches(pattern: &str, s: &str) -> bool {
    let mut piter = pattern.chars();
    let mut siter = s.chars();

    let mut pc = piter.next();
    let mut sc = siter.next();

    while pc.is_some() && sc.is_some() {
        let pcurr = pc.unwrap();
        let scurr = sc.unwrap();

        // Case 1: '*' is seen in pattern
        //     look at next char in pattern if any
        //     - if any chars left, grab that char and consume chars until that char is seen, if we exhaust 's' then no match
        //     - if none, short circuit. pattern ends in a '*' and matches the remaining string whatever it is
        if pcurr == '*' {
            pc = piter.next();
            // peek ahead
            if let Some(nc) = pc {
                if nc == '*' {
                    // special case '**', consume first '*' in pattern and cont
                    continue;
                }

                // consume chars in sc until that char is found or it is exhausted
                let pnext = pc.unwrap();
                while sc.is_some() && sc != Some(pnext) {
                    sc = siter.next();
                }
            } else {
                // pattern is exhausted and ends in a '*', short circuit because it matches anything remaining in 's'
                return true;
            }
        } else if pcurr != scurr {
            // Case 2: both pattern and incoming 's' chars are regular chars, compare 1-1 for equality
            return false;
        }

        pc = piter.next();
        sc = siter.next();
    }

    // one or more iterators is exhausted
    if pc.is_some() || sc.is_some() {
        return false;
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[test]
    fn test_matches() {
        let cases = vec![
            ("resources:blog:123", "resources:blog:123", true),
            ("re*123", "resources:blog:123", true),
            ("resources:blog:*", "resources:blog:123", true),
            ("resources:*", "resources:blog:123", true),
            ("resources:blog:123", "resources:blog:789", false),
            ("accounts:123", "resources:blog:789", false),
            ("actions:*:123", "actions:accounts:list:123", false),
            ("actions:*:list:*", "actions:accounts:list:123", true),
            ("actions:*:*:123", "actions:accounts:list:123", true),
            ("actions:**123", "actions:accounts:list:123", true),
        ];

        for x in cases {
            let (pattern, input, expected) = x;
            let actual = matches(pattern, input);
            assert_eq!(expected, actual, "pattern: {}, input: {}", pattern, input);
        }
    }

    #[bench]
    fn bench_match_wildcard(b: &mut Bencher) {
        let pattern = "actions:*:list:123";
        let input = "actions:accounts:list:123";
        b.iter(|| matches(pattern, input));
    }

    #[bench]
    fn bench_match_exact(b: &mut Bencher) {
        let pattern = "actions:accounts:list:123";
        let input = "actions:accounts:list:123";
        b.iter(|| matches(pattern, input));
    }
}
