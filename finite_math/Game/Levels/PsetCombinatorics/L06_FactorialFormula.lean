import Game.Metadata

World "PsetCombinatorics"
Level 6

Title "Factorial Formula Through Powerset"

Introduction "
# The Factorial Connection via Subsets

In BinomialCoefficients (Level 9), you proved the **factorial formula**:

$$\\binom{n}{k} \\cdot k! \\cdot (n-k)! = n!$$

This says: the number of $k$-element subsets times the ways to
arrange those $k$ elements times the ways to arrange the remaining
$n-k$ elements equals the total number of arrangements of all $n$
elements.

Now apply it with a **powerset layer**: given a finset $s$ with
$|s| = n$ and $3 \\le n$, prove:

$$|\\text{powersetCard } 3\\ s| \\cdot 3! \\cdot (n - 3)! = n!$$

**Strategy**:
1. Strip the powerset layer with `Finset.card_powersetCard` and `hs`
2. Apply `Nat.choose_mul_factorial_mul_factorial`
"

/-- The factorial formula through powerset counting. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) (h : 3 ≤ n) :
    (Finset.powersetCard 3 s).card * Nat.factorial 3 * Nat.factorial (n - 3) =
    Nat.factorial n := by
  Hint "Strip the powerset layer: convert
  `(powersetCard 3 s).card` to `choose n 3`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard, hs]`."
  rw [Finset.card_powersetCard, hs]
  Hint "The goal is `choose n 3 * 3! * (n - 3)! = n!`.

  This is the factorial formula `Nat.choose_mul_factorial_mul_factorial`
  with `k = 3`. It needs a proof that `3 ≤ n`."
  Hint (hidden := true) "Try `exact Nat.choose_mul_factorial_mul_factorial h`."
  exact Nat.choose_mul_factorial_mul_factorial h

Conclusion "
Strip-and-apply again: `card_powersetCard` converts the subset
count to `choose n 3`, then `choose_mul_factorial_mul_factorial`
closes it. The factorial formula says: choose 3 elements, arrange
them ($3!$ ways), arrange the rest ($(n-3)!$ ways) — every
permutation counted exactly once.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
