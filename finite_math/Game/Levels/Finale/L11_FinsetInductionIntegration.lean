import Game.Metadata

World "Finale"
Level 11

Title "Sum Distributes Over Addition"

Introduction "
# Finset Induction: Distributing a Sum

In the FinsetInduction world, you learned to prove identities about
finite sums by induction on the underlying `Finset`. Now apply that
technique in a new setting.

**Claim**: For any finset `s` and functions `f`, `g`:

$$\\sum_{i \\in s} (f(i) + g(i)) = \\sum_{i \\in s} f(i) + \\sum_{i \\in s} g(i)$$

This is the **additivity of summation** — a fundamental algebraic
identity that underlies linearity of expectation, linearity of the
trace (from the Matrix world), and much of linear algebra.

**The proof plan** uses finset induction:
1. **Base case** (`s = emptyset`): all three sums are 0
2. **Inductive step** (`insert a s`, `a notin s`):
   peel each sum with `sum_insert`, apply the IH, close with `ring`
"

/-- Summation distributes over addition. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ) :
    ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i := by
  Hint "Use finset induction on `s`."
  Hint (hidden := true) "Try:
  `induction s using Finset.induction_on with`
  `| empty`
  `| @insert a s ha ih`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: all three sums over the empty set are 0.
    Rewrite all three sums and close with `ring`."
    Hint (hidden := true) "Try `rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]`
    then `ring`."
    rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: peel each sum using `sum_insert ha`,
    then substitute the induction hypothesis `ih` and close with `ring`."
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]`
    then `ring`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    Hint "The goal is now an arithmetic identity involving addition.
    Close with `ring`."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
**Summation distributes over addition**:

$$\\sum_{i \\in s} (f(i) + g(i)) = \\sum_{i \\in s} f(i) + \\sum_{i \\in s} g(i)$$

| Case | Key rewrites | Closer |
|------|-------------|--------|
| Base | `sum_empty` (three times) | trivial |
| Step | `sum_insert ha` (three times) + `ih` | `ring` |

This identity is `Finset.sum_add_distrib` in Mathlib — here you
proved it by induction from scratch.

**The induction pattern**: Finset induction follows the same rhythm
as natural number induction from the SummationFormulas world:
- **Base**: clear with `sum_empty` (analogous to `sum_range_zero`)
- **Step**: peel with `sum_insert` (analogous to `sum_range_succ`),
  substitute the IH, close with algebra

**Connection to linearity**: This identity says that `fun f => sum f`
is an **additive** map. Combined with `sum_const_mul` (scaling), it
says summation is linear. This is the discrete analogue of the
integral's linearity: $\\int (f + g) = \\int f + \\int g$.
"

/-- `Finset.sum_add_distrib` proves that summation distributes over
addition: `∑ i in s, (f i + g i) = ∑ i in s, f i + ∑ i in s, g i`.

Disabled so you prove it by finset induction.
-/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "BigOp"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
DisabledTheorem Finset.sum_add_distrib
