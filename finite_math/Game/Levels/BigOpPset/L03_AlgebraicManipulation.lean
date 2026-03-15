import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 3

Title "Algebraic manipulation in a sum"

Introduction
"
## Level 3: Algebraic manipulation

Prove:
$$\\sum_{i=0}^{n-1} (5i + i^2) \\;=\\; 5\\sum_{i=0}^{n-1} i \\;+\\; \\sum_{i=0}^{n-1} i^2$$

This requires three moves:

1. **`sum_add_distrib`** — split the sum of `(5i + i²)` into two sums.
2. **`← mul_sum`** — pull the constant `5` out of `∑ (5 * i)`.

You also need to normalize `i ^ 2` inside the original sum to match.
Since `5 * i + i ^ 2` is already in a nice form, you may not even
need `sum_congr` — just the two algebraic lemmas.
"

/-- Decompose a sum of a mixed expression. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (5 * i + i ^ 2) =
    5 * (∑ i ∈ Finset.range n, i) + ∑ i ∈ Finset.range n, i ^ 2 := by
  Hint (hidden := true) "Split the sum using `rw [Finset.sum_add_distrib]`,
  then pull the constant out with `rw [← Finset.mul_sum]`."
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]

Conclusion
"
You decomposed a sum into structured parts using two moves:

1. **`sum_add_distrib`** — `∑ (f + g) = ∑ f + ∑ g`
2. **`← mul_sum`** — `∑ (c * f) = c * ∑ f`

These are the same techniques from the W15 boss, but applied to a
new expression (`5i + i²` instead of `3i + i²`).

**Retrieval check**: You retrieved V20 (algebraic manipulation in
big-operator goals) and L7 (`ring`-based reasoning) on a fresh
surface form.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
