import Game.Metadata

World "PsetCombinatorics"
Level 8

Title "Recognition Challenge"

Introduction "
# Which Identity?

Prove the following without being told which identity to use:

$$(n + 1) \\cdot \\binom{n}{1} = \\binom{n+1}{2} \\cdot 2$$

Your toolkit includes every identity from BinomialCoefficients.
Look at the structure of both sides. What pattern do you
recognize?
"

/-- A recognition challenge: identify and apply the right identity. -/
Statement (n : ℕ) :
    (n + 1) * Nat.choose n 1 = Nat.choose (n + 1) 2 * 2 := by
  Hint "Look at the left side: `(n + 1) * choose n k` with `k = 1`.
  Which identity from BinomialCoefficients has this shape on one
  side?"
  Hint (hidden := true) "This is the **absorption identity**:
  `Nat.add_one_mul_choose_eq` says `(n+1) * choose n k = choose (n+1) (k+1) * (k+1)`.
  Try `rw [Nat.add_one_mul_choose_eq]`."
  rw [Nat.add_one_mul_choose_eq]

Conclusion "
You recognized the absorption identity by its shape:
`(n+1) * choose n k` on one side. Pattern recognition — knowing
*which* tool to reach for — is the core pset skill.
"

/-- `Nat.choose_one_right` gives `Nat.choose n 1 = n`.

Disabled here to force recognition of the absorption pattern.
-/
TheoremDoc Nat.choose_one_right as "Nat.choose_one_right" in "Choose"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right Nat.choose_one_right
