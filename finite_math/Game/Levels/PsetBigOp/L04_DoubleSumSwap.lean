import Game.Metadata

World "PsetBigOp"
Level 4

Title "Double Sum Decomposition"

Introduction "
# Swapping a Double Sum

Prove:

$$\\sum_{x \\in s} \\Bigl(\\sum_{y \\in t} f(x,y) + g(x)\\Bigr) = 40$$

The key insight is that the double sum appears in the wrong order
to use the hypothesis `hswap`. You need:

- `Finset.sum_add_distrib` to separate the double sum from the
  single sum
- `Finset.sum_comm` to swap the summation order of the double sum
- Hypothesis substitution to close
"

/-- Swap a double sum and combine with a known single sum. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ)
    (hswap : ∑ y ∈ t, ∑ x ∈ s, f x y = 25)
    (hg : ∑ x ∈ s, g x = 15) :
    ∑ x ∈ s, (∑ y ∈ t, f x y + g x) = 40 := by
  Hint (hidden := true) "Use `rw [Finset.sum_add_distrib]` to split the
  summand into the double sum and the single sum."
  rw [Finset.sum_add_distrib]
  Hint (hidden := true) "The double sum has `x` first, `y` second. But
  `hswap` has `y` first. Use `rw [Finset.sum_comm]` to swap."
  rw [Finset.sum_comm]
  Hint (hidden := true) "Substitute the known values:
  `rw [hswap, hg]`."
  rw [hswap, hg]

Conclusion "
You proved the sum by decomposing and reordering:
1. `sum_add_distrib` separated the double sum from `g`
2. `sum_comm` swapped the summation order to match `hswap`
3. Hypothesis substitution closed the arithmetic

**When to swap**: If you have a double sum $\\sum_x \\sum_y f(x,y)$
and your information is about individual $y$-slices
($\\sum_x f(x,y)$ for each $y$), then swapping to
$\\sum_y \\sum_x f(x,y)$ lets you substitute directly.
This is the same reasoning that makes Fubini's theorem useful
in analysis — sometimes the integral (or sum) is easier in the
other order.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair
