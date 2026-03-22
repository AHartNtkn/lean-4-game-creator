import Game.Metadata

World "PsetCombinatorics"
Level 10

Title "Two-Identity Chain"

Introduction "
# Chaining Identities

Prove:

$$(n + 1) \\cdot |\\text{powersetCard } (n - 2)\\ s|
= 3 \\cdot \\binom{n+1}{3}$$

This requires chaining multiple identities. The first step is
familiar from previous levels. After that, the resulting
expression does not directly match any single identity — you
need to transform it first.

Only a starting hint is provided. Find the path yourself.
"

/-- Chain strip → symmetry → absorption to prove the identity. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) (h : 2 ≤ n) :
    (n + 1) * (Finset.powersetCard (n - 2) s).card = 3 * Nat.choose (n + 1) 3 := by
  Hint "Start with the strip-and-apply pattern: convert the
  powerset cardinality to a binomial coefficient."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard, hs]`."
  rw [Finset.card_powersetCard, hs]
  Hint "The goal is `(n+1) * choose n (n-2) = 3 * choose (n+1) 3`.

  Does `choose n (n-2)` match any identity directly? Or do you
  need to transform it first?"
  Hint (hidden := true) "Use symmetry to convert `choose n (n-2)` to `choose n 2`:
  `rw [Nat.choose_symm h]`. Then apply absorption."
  rw [Nat.choose_symm h]
  Hint (hidden := true) "Now apply `rw [Nat.add_one_mul_choose_eq]` and close with `ring`."
  rw [Nat.add_one_mul_choose_eq]
  ring

Conclusion "
You chained three moves: **strip** (powerset to choose),
**symmetry** (`choose n (n-2) = choose n 2`), then
**absorption** (`(n+1) * choose n 2 = choose (n+1) 3 * 3`).
Recognizing that symmetry was needed before absorption could
apply is the key transfer skill.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
