import Game.Metadata

World "PsetBigOp"
Level 2

Title "Union Sum with a Constant Offset"

Introduction "
# Split, Simplify, Substitute

Given two disjoint finsets with known sums for `f`, compute
$\\sum_{x \\in s \\cup t} (f(x) + 4)$.

You'll need three tools in the right order:
- `Finset.sum_add_distrib` to split the summand
- `Finset.sum_const` to simplify the constant part
- `Finset.sum_union h` to split the function sum over the union

**Order matters**: Apply `sum_const` before `sum_union`. If you
split the union first, both sums get split — leaving you with
four terms instead of three.
"

/-- Decompose a sum over a disjoint union with a constant offset. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ) (h : Disjoint s t)
    (hfs : ∑ x ∈ s, f x = 7) (hft : ∑ x ∈ t, f x = 8) :
    ∑ x ∈ s ∪ t, (f x + 4) = 15 + (s ∪ t).card • 4 := by
  Hint (hidden := true) "Use `rw [Finset.sum_add_distrib]` to split
  `f x + 4` into two separate sums."
  rw [Finset.sum_add_distrib]
  Hint (hidden := true) "Now simplify the constant sum with
  `rw [Finset.sum_const]` — this converts the sum of `4` to
  `(s ∪ t).card • 4`."
  rw [Finset.sum_const]
  Hint (hidden := true) "Split the function sum over the union:
  `rw [Finset.sum_union h, hfs, hft]`."
  rw [Finset.sum_union h, hfs, hft]

Conclusion "
You decomposed the sum in three steps:
1. `sum_add_distrib` split the summand into $\\sum f + \\sum 4$
2. `sum_const` simplified $\\sum 4$ to $|s \\cup t| \\cdot 4$
3. `sum_union h` split the function sum, then substitution closed it

**Why order matters**: If you applied `sum_union` first, both
$\\sum f$ and $\\sum 4$ would split — giving four terms instead of
three. Applying `sum_const` first eliminates the constant sum
before the union split touches it.

**The `•` notation**: For natural numbers, `n • m` is `n * m`.
`sum_const` produces `card • c` because it works over any additive
monoid, where `•` is the general repeated-addition operation.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
