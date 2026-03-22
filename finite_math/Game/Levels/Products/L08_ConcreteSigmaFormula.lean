import Game.Metadata

World "Products"
Level 8

Title "Sigma with Formula-Defined Fibers"

Introduction "
# Sigma with a Defined Fiber Family

In the previous level you computed the cardinality of a sigma
where the fiber sizes were given as hypotheses. Now let's work
with fibers defined by a **formula**.

Consider the index set `Finset.range 3 = {0, 1, 2}`, with fibers
`t i = Finset.range (i + 1)` — so fiber 0 has 1 element (`{0}`),
fiber 1 has 2 elements (`{0, 1}`), and fiber 2 has 3 elements
(`{0, 1, 2}`). The total:

$$|\\text{sigma}| = 1 + 2 + 3 = 6$$

This models a common combinatorial pattern: objects indexed by
a parameter, where the number of choices grows with the parameter.
For example, in a tournament with 3 rounds where round `i` offers
`i + 1` choices, the total number of (round, choice) pairs is 6.

**Your task**: Compute the cardinality of this sigma construction.
You'll use `Finset.card_sigma` to convert to a sum, then
`Finset.card_range` to evaluate each fiber size.
"

/-- Compute sigma cardinality with formula-defined fibers. -/
Statement :
    ((Finset.range 3).sigma (fun i => Finset.range (i + 1))).card = 6 := by
  Hint "Apply `Finset.card_sigma` to convert the sigma cardinality
  into a sum of fiber sizes."
  Hint (hidden := true) "Try `rw [Finset.card_sigma]`."
  rw [Finset.card_sigma]
  Hint "Now evaluate the sum over `Finset.range 3`. Peel off terms
  from the top with `Finset.sum_range_succ`."
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` to peel off
  the `i = 2` term."
  rw [Finset.sum_range_succ]
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` again for
  the `i = 1` term."
  rw [Finset.sum_range_succ]
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` once more
  for `i = 0`."
  rw [Finset.sum_range_succ]
  Hint "The sum over `Finset.range 0` is 0."
  Hint (hidden := true) "Try `rw [Finset.sum_range_zero]`."
  rw [Finset.sum_range_zero]
  Hint "Now simplify each `(Finset.range k).card` to `k` using
  `Finset.card_range`."
  Hint (hidden := true) "Try `rw [Finset.card_range, Finset.card_range, Finset.card_range]`."
  rw [Finset.card_range, Finset.card_range, Finset.card_range]

Conclusion "
$|\\text{sigma}| = \\sum_{i=0}^{2} |\\text{range}(i+1)| = 1 + 2 + 3 = 6$

Unlike the previous level where fiber sizes were given as hypotheses,
here you computed each fiber size directly from `Finset.card_range`.
The fibers are **defined**, not just hypothesized — each one is a
concrete finset whose size Lean can compute.

**The pattern**: `card_sigma` converts to a sum, then you evaluate
the sum term by term. When fibers are formula-defined, you use the
relevant cardinality lemma (here `card_range`) to compute each
fiber's contribution.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
