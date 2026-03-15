import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 2

Title "Product by induction"

Introduction
"
## Level 2: A product identity by induction

Prove by induction:

$$\\prod_{i=0}^{n-1} 3 \\;=\\; 3^n$$

This is the product of `n` copies of `3`. The proof follows the
multiplicative analogue of the induction pattern: use
`prod_range_succ` to peel off the last factor, then apply the
inductive hypothesis.
"

/-- The product of `n` copies of `3` is `3 ^ n`. -/
Statement (n : Nat) : ∏ i ∈ Finset.range n, (3 : Nat) = 3 ^ n := by
  Hint (hidden := true) "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "The base case: `∏ i ∈ range 0, 3 = 3 ^ 0`.
    Both sides reduce to `1`. Use `rfl`."
    rfl
  | succ n ih =>
    Hint (hidden := true) "Peel off the last factor with
    `rw [Finset.prod_range_succ]`, apply `ih`, then `ring`."
    rw [Finset.prod_range_succ, ih]
    ring

Conclusion
"
You proved a multiplicative induction identity. The pattern mirrors
the additive case:

1. **`induction n with`**
2. **`rfl`** for the base case (empty product is `1`, and `3^0 = 1`)
3. **`rw [prod_range_succ, ih]`** then **`ring`**

**Retrieval check**: You retrieved M25 (range-based big-operator
patterns) in the multiplicative setting.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
