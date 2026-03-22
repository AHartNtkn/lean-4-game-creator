import Game.Metadata

World "FinsetInduction"
Level 5

Title "Algebra in the Inductive Step"

Introduction "
# ring Meets Induction

In the previous level, the arithmetic in the inductive step was
simple enough for `omega` ($1 + |s| = |s| + 1$). But many sum
identities require genuine algebraic manipulation.

The workhorse pattern:
1. **Peel** with `sum_insert ha`
2. **Apply** the induction hypothesis `ih`
3. **Close** with `ring`

`ring` handles any polynomial identity: commutativity, associativity,
distributivity, collecting like terms. It treats opaque terms like
`f a` and `\\sum_{x \\in s} f(x)` as variables and manipulates the
algebra.

**Your task**: Prove that
$\\sum_{x \\in s} (f(x) + f(x)) = 2 \\cdot \\sum_{x \\in s} f(x)$
by finset induction. You practiced the base case and inductive step
separately in L02-L03 — now combine them.
"

/-- The sum of f + f equals twice the sum of f. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, (f x + f x) = 2 * ∑ x ∈ s, f x := by
  Hint "Start with finset induction on `s`."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: Rewrite both sums over `∅` to `0`,
    then close the arithmetic."
    Hint (hidden := true) "Try `rw [Finset.sum_empty, Finset.sum_empty]`
    then `ring`."
    rw [Finset.sum_empty, Finset.sum_empty]
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: Peel both sums, apply the IH, then
    close with `ring`.

    Remember: `sum_insert ha` must be applied to *both* sums
    (both the left side `∑ (f x + f x)` and the right side
    `∑ f x`)."
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]`
    then `ring`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    Hint "The goal is
    `f a + f a + 2 * ∑ f = 2 * (f a + ∑ f)`.
    This is pure algebra — `ring` closes it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
The **peel-IH-ring** pattern is the standard approach for algebraic
sum identities proved by finset induction:

1. `rw [Finset.sum_insert ha]` — peel each sum over `insert a s`
2. `rw [ih]` — substitute the induction hypothesis
3. `ring` — close the algebra

For the base case, the pattern is simpler: `sum_empty` on each sum,
then `ring` (or `rfl` if both sides reduce to `0`).

You'll use this pattern for every sum identity in this world and
in the SummationFormulas world that follows.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub
