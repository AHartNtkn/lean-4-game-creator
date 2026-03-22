import Game.Metadata

World "BigOpAlgebra"
Level 9

Title "Counting with Filters"

Introduction "
# How Many Elements Satisfy a Predicate?

Given a finset `s` and a predicate `p`, the number of elements
satisfying `p` is `(s.filter p).card`. But you already know two
tools that connect cardinality and summation:

- `card_eq_sum_ones`: `s.card = ∑ x ∈ s, 1`
- `sum_filter`: `∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0`

Combining them reveals that the count of elements satisfying `p`
equals a conditional sum of 1s:

$$|\\{x \\in s \\mid p(x)\\}| = \\sum_{x \\in s} \\begin{cases} 1 & \\text{if } p(x) \\\\ 0 & \\text{otherwise} \\end{cases}$$

This is a fundamental identity in combinatorics: **counting is
summing indicator functions**.

**Your task**: Given the conditional count, prove the cardinality
equals that count. This requires `card_eq_sum_ones` to expand
cardinality into a sum, then `sum_filter` to convert the filtered
sum into a conditional sum.
"

/-- Cardinality of a filter equals the conditional sum of 1s. -/
Statement (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (h : ∑ x ∈ s, (if p x then (1 : ℕ) else 0) = 7) :
    (s.filter p).card = 7 := by
  Hint "Expand `(s.filter p).card` into a sum of 1s using
  `rw [Finset.card_eq_sum_ones]`."
  rw [Finset.card_eq_sum_ones]
  Hint "Now convert the filtered sum `∑ x ∈ s.filter p, 1` into
  a conditional sum over `s` using `rw [Finset.sum_filter]`."
  Hint (hidden := true) "Try `rw [Finset.sum_filter]`."
  rw [Finset.sum_filter]
  Hint "The goal matches hypothesis `h`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
You just proved that counting elements satisfying `p` is the same
as summing 1s conditionally — **counting is summation of indicator
functions**.

This combination of `card_eq_sum_ones` + `sum_filter` appears
frequently in combinatorics: whenever you need to count elements
satisfying a property, you can express the count as a sum and then
manipulate it algebraically using all the tools from this world
(`sum_add_distrib`, `sum_union`, etc.).
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
