import data.set.basic -- hide
open set -- hide

/- Tactic : exfalso

## Summary

Changes the goal to `⊢ false`.

## Details

This may seem hard to prove,
but it is useful when we have a contradiction in the hypotheses.

For example, if we have `h : ¬ P` as a hypothesis and we apply `exfalso`
we can then `apply h` to transform the goal into `⊢ P`.
-/


/- Hint : Click here for a hint, in case you get stuck.
In Lean, the  negation `¬ P` of a statement is a shorthand for `P → false`. Therefore
start with `exfalso`, and remember that negation is the same as `→ false`.
-/

