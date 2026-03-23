import Game.Metadata

World "Finale"
Level 2

Title "Powerset Partition by Size"

Introduction "
# Three Roads to $2^n$

The powerset of an $n$-element set has $2^n$ elements. We also
know that $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$ (the row sum
of Pascal's triangle).

These are the *same fact*. The powerset partitions into subsets
of size 0, size 1, ..., size $n$. The number of size-$k$ subsets
is $\\binom{n}{k}$. Summing over all sizes recovers $2^n$.

Prove this directly:

$$\\sum_{k=0}^{n} |\\{\\text{size-}k \\text{ subsets of range } n\\}| = 2^n$$
"

/-- The sum of the sizes of k-element-subset families equals 2^n. -/
Statement (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((Finset.range n).powersetCard k).card = 2 ^ n := by
  Hint "Each `(range n).powersetCard k` is the family of size-`k`
  subsets of `range n`. What does its cardinality equal in terms of
  `Nat.choose`?"
  Hint (hidden := true) "Prove a helper:
  `have h : forall k in Finset.range (n + 1), ((Finset.range n).powersetCard k).card = Nat.choose n k := by`
  `  intro k _`
  `  rw [Finset.card_powersetCard, Finset.card_range]`"
  have h : ∀ k ∈ Finset.range (n + 1),
      ((Finset.range n).powersetCard k).card = Nat.choose n k := by
    intro k _
    rw [Finset.card_powersetCard, Finset.card_range]
  Hint "Now rewrite the sum using `Finset.sum_congr rfl h` to
  replace each summand with `Nat.choose n k`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl h]`."
  rw [Finset.sum_congr rfl h]
  Hint "The goal is now a well-known identity. Which lemma from
  the BinomialCoefficients world gives the row sum of Pascal's
  triangle?"
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion "
$$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$$

This proof connects three different perspectives on $2^n$:
- **Type theory** (Phase 3): `card (Fin n -> Fin 2) = 2^n`
- **Powerset** (Phase 5): `s.powerset.card = 2^(s.card)`
- **Binomial coefficients** (Phase 5): `sum choose n k = 2^n`

They are all the same fact: the $2^n$ subsets of an $n$-element
set can be counted as functions to Bool, as the powerset, or as
the sum over subset sizes.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
