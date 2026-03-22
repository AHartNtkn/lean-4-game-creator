import Game.Metadata

World "BinomialTheorem"
Level 9

Title "Powerset Meets Row Sum"

Introduction "
# Double Counting: Powerset = Row Sum

In the Powerset world, you learned two facts:
- `Finset.card_powerset`: a set with $n$ elements has $2^n$ subsets
- `Finset.card_powersetCard`: the $k$-element subsets number $\\binom{n}{k}$

In Level 8, you derived:
- `Nat.sum_range_choose`: $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$

These are the same fact viewed from different angles:

$$\\underbrace{|\\mathcal{P}(s)|}_{2^n} = \\sum_{k=0}^{n} \\underbrace{|\\text{powersetCard } k\\ s|}_{\\binom{n}{k}} = \\underbrace{\\sum_{k=0}^{n} \\binom{n}{k}}_{2^n}$$

**Your task**: Prove that the sum of subset counts by size equals
the total powerset cardinality. This requires three tools:
1. `Finset.card_powerset` to handle the RHS
2. `Finset.card_powersetCard` to simplify each summand
3. `Nat.sum_range_choose` to close
"

/-- The sum of k-element subset counts equals the powerset size. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) :
    ∑ k ∈ Finset.range (n + 1), (Finset.powersetCard k s).card =
    s.powerset.card := by
  Hint "Start by simplifying the RHS. Use `rw [Finset.card_powerset]`
  to replace `s.powerset.card` with `2 ^ s.card`."
  Hint (hidden := true) "Try `rw [Finset.card_powerset, hs]`."
  rw [Finset.card_powerset, hs]
  Hint "The RHS is now `2 ^ n`. For the LHS, each
  `(powersetCard k s).card` equals `Nat.choose s.card k` by
  `card_powersetCard`. Use the `have` + `sum_congr` pattern to
  rewrite each summand."
  Hint (hidden := true) "Declare:
  `have simpl : ∀ k ∈ Finset.range (n + 1), (Finset.powersetCard k s).card = Nat.choose n k := by`

  Then: `intro k _` followed by `rw [Finset.card_powersetCard, hs]`."
  have simpl : ∀ k ∈ Finset.range (n + 1),
      (Finset.powersetCard k s).card = Nat.choose n k := by
    intro k _
    rw [Finset.card_powersetCard, hs]
  Hint "Good — `simpl` proves each summand equals `choose n k`.
  Now rewrite the sum with `rw [Finset.sum_congr rfl simpl]`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl]`."
  rw [Finset.sum_congr rfl simpl]
  Hint "The goal is `∑ k, choose n k = 2 ^ n`. This is exactly
  `Nat.sum_range_choose` from Level 8."
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion "
You connected three results into one chain:

$$\\sum_{k=0}^{n} |\\text{powersetCard } k\\ s|
\\;\\xrightarrow{\\text{card\\_powersetCard}}\\;
\\sum_{k=0}^{n} \\binom{n}{k}
\\;\\xrightarrow{\\text{sum\\_range\\_choose}}\\;
2^n
\\;\\xleftarrow{\\text{card\\_powerset}}\\;
|\\mathcal{P}(s)|$$

**The counting interpretation**: A set with $n$ elements has $2^n$
subsets in total (by `card_powerset`). Grouping subsets by size,
there are $\\binom{n}{k}$ subsets of size $k$ (by `card_powersetCard`).
Summing over all sizes gives $\\sum \\binom{n}{k} = 2^n$
(by `sum_range_choose`).

This is a **double counting** argument: the same quantity ($2^n$)
is computed two ways — once by `card_powerset` and once by summing
`card_powersetCard` over all sizes.

**Skills used**: `sum_congr rfl` (BigOpAlgebra), `card_powerset`
and `card_powersetCard` (Powerset), `sum_range_choose` (Level 8).

**Two proofs of one fact**: You now have two genuinely different proofs
that $\\sum \\binom{n}{k} = 2^n$. The algebraic proof (Level 8) works
by specializing the binomial theorem — pure symbol manipulation. The
combinatorial proof (this level) counts subsets — each element is either
in or out, giving $2$ choices per element, hence $2^n$ total subsets.
Both arrive at the same number by completely different reasoning.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
