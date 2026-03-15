import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 2

Title "sum_empty"

Introduction
"
# The sum over the empty set

What happens when you sum over no elements at all? The answer is the
identity for addition: `0`.

```
Finset.sum_empty : ∑ x ∈ ∅, f x = 0
```

This is the **base case** for any inductive argument about sums. Just
as `Finset.card_empty` tells you `(∅ : Finset α).card = 0`, the sum
over the empty finset gives you the additive identity.

## Your task

Prove that `∑ x ∈ (∅ : Finset Nat), (x ^ 2) = 0`.
"

/-- The sum of `x ^ 2` over the empty finset is `0`. -/
Statement : ∑ x ∈ (∅ : Finset Nat), (x ^ 2) = 0 := by
  Hint "The sum over the empty set is `0`, regardless of the function.
  Use `exact Finset.sum_empty` or `rw [Finset.sum_empty]`."
  Hint (hidden := true) "Try `exact Finset.sum_empty`."
  exact Finset.sum_empty

Conclusion
"
The sum over the empty finset is always `0`:

```
Finset.sum_empty : ∑ x ∈ ∅, f x = 0
```

This holds for *any* function `f`, because there are no elements to
add up, and the empty sum is the additive identity.

**In plain language**: \"An empty sum is zero, just as an empty product
is one. This is a convention, but it is the only one that makes the
recursive definition work.\"
"

/-- `Finset.sum_empty` states that `∑ x ∈ ∅, f x = 0`.

The sum over the empty finset is the additive identity. -/
TheoremDoc Finset.sum_empty as "Finset.sum_empty" in "Finset"

NewTheorem Finset.sum_empty
DisabledTactic trivial decide native_decide simp aesop simp_all
