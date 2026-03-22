import Game.Metadata

World "PsetCombinatorics"
Level 1

Title "Backward Pascal"

Introduction "
# Warm-Up: Backward Pascal

In the BinomialCoefficients world, you used Pascal's identity to
**expand** a binomial coefficient:

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

Here you need the **reverse** direction: given a sum of two
binomial coefficients, **fold** them into one.

Prove that three consecutive entries from two adjacent rows
telescope:

$$\\binom{n}{k} + \\binom{n}{k+1} + \\binom{n+1}{k+2} = \\binom{n+2}{k+2}$$

**Strategy**: Apply `← Nat.choose_succ_succ` twice.
The first application folds the first two terms into
`choose (n+1) (k+1)`. The second folds the result with the
third term into `choose (n+2) (k+2)`.
"

/-- Three-term Pascal telescoping. -/
Statement (n k : ℕ) :
    Nat.choose n k + Nat.choose n (k + 1) + Nat.choose (n + 1) (k + 2) =
    Nat.choose (n + 2) (k + 2) := by
  Hint "The first two terms `choose n k + choose n (k+1)` match
  Pascal's identity read backwards. Use `← Nat.choose_succ_succ`
  to fold them into `choose (n+1) (k+1)`."
  Hint (hidden := true) "Try `rw [← Nat.choose_succ_succ]`."
  rw [← Nat.choose_succ_succ]
  Hint "Now the goal is
  `choose (n+1) (k+1) + choose (n+1) (k+2) = choose (n+2) (k+2)`.

  This is again Pascal's identity read backwards. Apply the same
  rewrite one more time."
  Hint (hidden := true) "Try `rw [← Nat.choose_succ_succ]` again."
  rw [← Nat.choose_succ_succ]

Conclusion "
Two backward rewrites, and three terms collapse to one.

`← Nat.choose_succ_succ` folds `choose n k + choose n (k+1)`
into `choose (n+1) (k+1)`. Pascal's identity reads in both
directions: forward *expands*, backward *folds*. Repeated
folding produces telescoping identities like this one.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
