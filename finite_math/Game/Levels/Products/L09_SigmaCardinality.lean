import Game.Metadata

World "Products"
Level 9

Title "Sigma Cardinality"

Introduction "
# Counting Dependent Pairs

You just used `Finset.card_sigma` to evaluate a sigma cardinality
by unfolding the sum. Now let's go the other direction: given
information about the **sum**, conclude the sigma cardinality.

Recall:
$$|s.\\text{sigma}\\ t| = \\sum_{i \\in s} |t\\, i|$$

**Your task**: Given that the sum of the fiber sizes is 10,
conclude that the sigma has 10 elements.
"

/-- Compute sigma cardinality from the fiber-size sum. -/
Statement (s : Finset ℕ) (t : ℕ → Finset ℕ)
    (hsum : ∑ a ∈ s, (t a).card = 10) :
    (s.sigma t).card = 10 := by
  Hint "Apply `Finset.card_sigma` to convert the sigma cardinality
  into a sum of fiber sizes."
  Hint (hidden := true) "Try `rw [Finset.card_sigma]`."
  rw [Finset.card_sigma]
  Hint "Now the goal is `∑ a ∈ s, (t a).card = 10`, which is
  exactly your hypothesis `hsum`."
  Hint (hidden := true) "Try `exact hsum`."
  exact hsum

Conclusion "
`Finset.card_sigma` reduces a sigma cardinality question to a
summation question:

$$|s.\\text{sigma}\\ t| = \\sum_{i \\in s} |t\\, i|$$

**Connection to products**: If every `t i` has the same size `k`,
then $\\sum_{i \\in s} k = |s| \\cdot k$, recovering `card_product`.
Sigma is the generalization — products are the uniform special case.

**Connection to big operators**: You already know how to evaluate
sums over explicit finsets (`sum_range_succ`, `sum_insert`,
`sum_singleton`). Those same tools apply to sigma cardinalities.

**The disjoint union reading**: You can think of `s.sigma t`
as a *disjoint union* of the fibers `t i` over `i ∈ s`. Each
fiber contributes `(t i).card` elements, and the fibers don't
overlap (they live in different components of the sigma type).
The cardinality formula `card_sigma` is then just the additive
rule for disjoint unions: total = sum of parts. You'll see this
same principle again later when the diagonal and off-diagonal
partition `s ×ˢ s` — the partition-then-count pattern.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
