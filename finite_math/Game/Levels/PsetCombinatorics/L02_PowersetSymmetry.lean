import Game.Metadata

World "PsetCombinatorics"
Level 2

Title "Powerset Symmetry"

Introduction "
# Subset Counting via Symmetry

In the Powerset world, you learned that `Finset.card_powersetCard`
converts a subset count to a binomial coefficient:

$$|\\text{powersetCard } k\\ s| = \\binom{|s|}{k}$$

In the BinomialCoefficients world, you learned the symmetry identity:

$$\\binom{n}{k} = \\binom{n}{n-k}$$

Now combine them: show that counting $k$-element subsets and
$(n-k)$-element subsets gives twice the binomial coefficient.

Given a finset $s$ with $|s| = n$ and $2 \\le n$, prove:

$$|\\text{powersetCard } 2\\ s| + |\\text{powersetCard } (n - 2)\\ s|
= 2 \\cdot \\binom{n}{2}$$
"

/-- Subset symmetry: 2-element and (n-2)-element subsets. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) (h : 2 ≤ n) :
    (Finset.powersetCard 2 s).card + (Finset.powersetCard (n - 2) s).card =
    2 * Nat.choose n 2 := by
  Hint "First, convert both powerset cardinalities to binomial
  coefficients using `Finset.card_powersetCard`, then substitute
  `s.card` with `n` using `hs`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard, Finset.card_powersetCard, hs]`."
  rw [Finset.card_powersetCard, Finset.card_powersetCard, hs]
  Hint "The goal is `choose n 2 + choose n (n - 2) = 2 * choose n 2`.

  The two terms on the left are the **same** by symmetry:
  `choose n (n - 2) = choose n 2` because choosing which
  $n - 2$ elements to **include** is the same as choosing which
  $2$ to **exclude**.

  Use `Nat.choose_symm h` to rewrite `choose n (n - 2)` to
  `choose n 2`."
  Hint (hidden := true) "Try `rw [Nat.choose_symm h]`."
  rw [Nat.choose_symm h]
  Hint "The goal is `choose n 2 + choose n 2 = 2 * choose n 2`.
  Close with `ring`."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
You proved that counting $2$-element and $(n-2)$-element subsets
gives $2 \\cdot \\binom{n}{2}$.

This proof demonstrates the **strip-and-apply** pattern you will
use throughout this problem set: **strip** the powerset layer
with `Finset.card_powersetCard` + `rw [hs]` to get binomial
coefficients, then **apply** an algebraic identity (`choose_symm`
here). Choosing which elements to include is the same as choosing
which to exclude — that bijection is why symmetry holds.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
