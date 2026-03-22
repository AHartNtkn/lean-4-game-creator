import Game.Metadata

World "PsetCombinatorics"
Level 13

Title "Pointwise Rewriting in Sums"

Introduction "
# Rewriting Inside a Sum

When your goal has `∑ p ∈ S, f(p) = ∑ p ∈ S, g(p)`, you can
reduce it to a pointwise proof `∀ p ∈ S, f(p) = g(p)` using
`Finset.sum_congr rfl`.

The pattern:
1. Declare a `have` proving the pointwise equality
2. Apply `rw [Finset.sum_congr rfl ...]` to transform the sum

Prove that summing subset counts over the antidiagonal gives $2^n$:

$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)}
|\\text{powersetCard } i\\ s| = 2^n$$
"

/-- Strip powerset counts inside a sum using sum_congr rfl. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) :
    ∑ p ∈ Finset.antidiagonal n,
      (Finset.powersetCard p.1 s).card = 2 ^ n := by
  Hint "First, prove that each summand equals `choose n p.1`.
  Declare a `have` with type
  `∀ p ∈ Finset.antidiagonal n, ... = Nat.choose n p.1`."
  Hint (hidden := true) "Try:
  `have simpl : ∀ p ∈ Finset.antidiagonal n, (Finset.powersetCard p.1 s).card = Nat.choose n p.1 := by`
  `  intro p _`
  `  rw [Finset.card_powersetCard, hs]`"
  have simpl : ∀ p ∈ Finset.antidiagonal n,
      (Finset.powersetCard p.1 s).card = Nat.choose n p.1 := by
    intro p _
    rw [Finset.card_powersetCard, hs]
  Hint "Now apply `Finset.sum_congr rfl` to rewrite the whole sum,
  then reindex and apply the row sum identity."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`."
  rw [Finset.sum_congr rfl simpl, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion "
You used `sum_congr rfl` to strip `card_powersetCard` inside
a sum — the same pattern the boss requires, but there you will
strip *products* of powerset counts pointwise.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
