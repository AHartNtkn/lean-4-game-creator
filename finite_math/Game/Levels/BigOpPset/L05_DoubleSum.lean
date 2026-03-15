import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 5

Title "Double sum interchange"

Introduction
"
## Level 5: Interchange a double sum

In W16 you used `Finset.sum_comm` to swap the order of summation
over `range 3 × range 4`. Now do the same in a different context:
a double sum of a product `f i * g j`.

Prove:
$$\\sum_{i=0}^{n-1} \\sum_{j=0}^{m-1} f(i) \\cdot g(j)
\\;=\\; \\sum_{j=0}^{m-1} \\sum_{i=0}^{n-1} f(i) \\cdot g(j)$$
"

/-- Interchange summation order in a product of functions. -/
Statement (n m : Nat) (f g : Nat → Nat) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i * g j =
    ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n, f i * g j := by
  Hint (hidden := true) "Use `exact Finset.sum_comm` to swap the
  summation order."
  exact Finset.sum_comm

Conclusion
"
You interchanged summation order using `Finset.sum_comm`. The
summand `f i * g j` made this look more complex than the earlier
exercise, but `sum_comm` handles it identically — the function's
structure does not matter.

**Retrieval check**: You retrieved M26 (`sum_comm` for double sums)
on a product-of-functions surface form.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
