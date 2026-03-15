import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 2

Title "Finsupp.single: construction and evaluation"

Introduction
"
# Building a `Finsupp` with `single`

In the previous level you evaluated `Finsupp.single 3 5` at the point `3`.
Now you will verify that `Finsupp.single` does what it promises: it sends
its base point to the given value, and all other points to zero.

## Recap

The evaluation rule is:
```
Finsupp.single_apply : (Finsupp.single a b) a' = if a = a' then b else 0
```

When the condition `a = a'` is true, use `if_pos` to resolve the conditional.
When it is false, use `if_neg` to resolve it.

## Resolving `if_neg`

When the condition is false, you need to supply a proof of the negation.
For concrete natural numbers like `1 ≠ 2`, the tactic `omega` can close
such goals.

So the pattern is: `rw [if_neg (by omega)]`.

## Your task

Prove both claims about `Finsupp.single 1 7`:
1. It sends `1` to `7`.
2. It sends `2` to `0`.

Use `constructor` to split the conjunction, then `rw [Finsupp.single_apply]`
followed by `if_pos` or `if_neg` in each branch.
"

/-- `Finsupp.single 1 7` sends `1` to `7` and `2` to `0`. -/
Statement : (Finsupp.single 1 (7 : ℕ)) 1 = 7 ∧ (Finsupp.single 1 (7 : ℕ)) 2 = 0 := by
  Hint "Start with `constructor` to split the conjunction into two goals."
  constructor
  · Hint "For the first goal, use `rw [Finsupp.single_apply]` to unfold,
    then `rw [if_pos rfl]` since `1 = 1`."
    Hint (hidden := true) "Try `rw [Finsupp.single_apply, if_pos rfl]`."
    rw [Finsupp.single_apply, if_pos rfl]
  · Hint "For the second goal, use `rw [Finsupp.single_apply]` to unfold,
    then `rw [if_neg (by omega)]` since `1 ≠ 2`.

    The `by omega` inside `if_neg` proves `¬(1 = 2)` automatically."
    Hint (hidden := true) "Try `rw [Finsupp.single_apply, if_neg (by omega)]`."
    rw [Finsupp.single_apply, if_neg (by omega)]

Conclusion
"
You verified both properties of `Finsupp.single 1 7`:
- At the base point `1`, it returns the value `7`.
- At a different point `2`, it returns `0`.

## The two-case pattern

Evaluating `Finsupp.single a b` always follows the same pattern:
1. `rw [Finsupp.single_apply]` to get the conditional.
2. `rw [if_pos ...]` if the point equals `a`, or `rw [if_neg ...]` if not.

For concrete numbers, `rfl` proves equality and `by omega` proves
inequality.

**In plain language**: \"`Finsupp.single a b` is the function that says
'b at a, zero everywhere else.' Evaluating it is just checking whether
you are at a or not.\"
"

TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
