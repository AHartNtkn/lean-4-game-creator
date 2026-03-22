import Game.Metadata

World "BinomialCoefficients"
Level 7

Title "Boundary Revisited"

Introduction "
# Deriving $\\binom{n}{n} = 1$ from Symmetry

In Level 1, we gave you `Nat.choose_self` ($\\binom{n}{n} = 1$) as a fact.
But now that you have **symmetry**, you can *derive* it!

The key insight: the two boundary values aren't independent.
$$\\binom{n}{n} \\stackrel{\\text{symm}}{=} \\binom{n}{0} \\stackrel{\\text{zero\\_right}}{=} 1$$

Choosing all $n$ items is the same as leaving out $0$ items, which
gives $\\binom{n}{0} = 1$.

## New tool: Backward rewrite

You know `rw [h]` rewrites the **left** side of `h` to the right side.
Sometimes you need the reverse: `rw [\\leftarrow h]` (written `rw [← h]`)
rewrites the **right** side to the left side.

For example, if `h : A = B`, then:
- `rw [h]` replaces `A` with `B` in the goal
- `rw [← h]` replaces `B` with `A` in the goal

**Your task**: Prove $\\binom{n}{n} = 1$ using `← Nat.choose_zero_right`
and `Nat.choose_symm` — without using `Nat.choose_self`.
"

/-- C(n, n) = 1, derived from symmetry and choose_zero_right. -/
Statement (n : ℕ) : Nat.choose n n = 1 := by
  Hint "The goal is `Nat.choose n n = 1`. We want to connect this
  to `Nat.choose n 0 = 1` via symmetry.

  Step 1: Use backward rewrite to replace the `1` with `Nat.choose n 0`.
  Since `Nat.choose_zero_right n : Nat.choose n 0 = 1`, writing
  `rw [← Nat.choose_zero_right n]` replaces `1` with `Nat.choose n 0`."
  Hint (hidden := true) "Try `rw [← Nat.choose_zero_right n]`."
  rw [← Nat.choose_zero_right n]
  Hint "The goal is now `Nat.choose n n = Nat.choose n 0`.
  This is exactly what symmetry says (with k = 0).
  Create a proof that `0 ≤ n` with `have`, then apply symmetry."
  Hint (hidden := true) "Try `have h : 0 ≤ n := by omega`."
  have h : 0 ≤ n := by omega
  Hint "Now use `exact Nat.choose_symm h` to close the goal."
  Hint (hidden := true) "Try `exact Nat.choose_symm h`."
  exact Nat.choose_symm h

Conclusion "
You just proved that `choose_self` is a **consequence** of
`choose_zero_right` + `choose_symm`:
$$\\binom{n}{n} \\stackrel{\\text{symm}}{=} \\binom{n}{0} \\stackrel{\\text{zero\\_right}}{=} 1$$

This is a recurring theme in mathematics: results that *look*
independent often turn out to be connected. The two boundary values
of Pascal's triangle — both edges being $1$ — are really the *same*
fact viewed through the lens of symmetry.

You learned a new tool: **backward rewrite** (`rw [← h]`). This is
useful whenever you want to *introduce* a known expression rather than
*simplify* one away.

You can still use `choose_self` directly in future levels (it's more
convenient than re-deriving it each time). But knowing *why* it's
true gives you deeper understanding.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_self Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
