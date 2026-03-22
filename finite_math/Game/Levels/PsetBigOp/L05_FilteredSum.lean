import Game.Metadata

World "PsetBigOp"
Level 5

Title "Filtered Sum Conversion"

Introduction "
# Combining a Filtered Sum with a Full Sum

Prove:

$$\\sum_{x \\in s} \\bigl(\\mathbb{1}_{p}(x) \\cdot f(x) + g(x)\\bigr) = 30$$

where the indicator function gives $f(x)$ when $p(x)$ holds and
$0$ otherwise.

You'll need:
- `Finset.sum_add_distrib` to separate the conditional part from `g`
- `Finset.sum_filter` (backwards) to convert the conditional sum
  to a filtered-finset sum: `\\sum_{x \\in s, p(x)} f(x)`
- Hypothesis substitution
"

/-- Convert a conditional sum to a filtered sum and combine. -/
Statement (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f g : ℕ → ℕ)
    (hfp : ∑ x ∈ s.filter p, f x = 20)
    (hg : ∑ x ∈ s, g x = 10) :
    ∑ x ∈ s, ((if p x then f x else 0) + g x) = 30 := by
  Hint (hidden := true) "Use `rw [Finset.sum_add_distrib]` to split the
  summand into the conditional part and the `g` part."
  rw [Finset.sum_add_distrib]
  Hint (hidden := true) "The first sum is `∑ x ∈ s, if p x then f x else 0`.
  Use `rw [← Finset.sum_filter]` to convert it to
  `∑ x ∈ s.filter p, f x`."
  rw [← Finset.sum_filter]
  Hint (hidden := true) "Substitute the known values:
  `rw [hfp, hg]`."
  rw [hfp, hg]

Conclusion "
You combined a filtered sum with a full sum in three steps:
1. `sum_add_distrib` separated the conditional term from `g`
2. `← sum_filter` converted the if-then-else sum to a filtered sum
3. Hypothesis substitution closed the arithmetic

**Both directions of `sum_filter`**:
- Forward (`rw [sum_filter]`): filtered sum → conditional sum
- Backward (`rw [← sum_filter]`): conditional sum → filtered sum

In BigOpAlgebra, you used the forward direction. Here, the backward
direction is needed because the hypothesis `hfp` is stated in terms
of the filtered finset. Recognizing which direction to use —
matching the form of your hypotheses — is a key retrieval skill.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_ite
