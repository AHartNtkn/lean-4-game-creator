import Game.Metadata

World "BinomialCoefficients"
Level 5

Title "Applying the Boundary Theorems"

Introduction "
# Applying All Three Boundary Theorems

In Levels 1–4, you learned the three boundary theorems and saw Pascal's
identity in action on a concrete computation:
- `Nat.choose_zero_right`: $\\binom{n}{0} = 1$
- `Nat.choose_one_right`: $\\binom{n}{1} = n$
- `Nat.choose_self`: $\\binom{n}{n} = 1$

Now apply all three on a **variable** statement. Row $n + 1$ of
Pascal's triangle starts with $\\binom{n+1}{1} = n + 1$, has
$\\binom{n+1}{0} = 1$ in position zero, and ends with
$\\binom{n+1}{n+1} = 1$. Adding these gives:

$$\\binom{n+1}{1} + \\binom{n+1}{0} + \\binom{n+1}{n+1} = n + 3$$

**Strategy**: Rewrite each `Nat.choose` term one at a time using
the appropriate boundary theorem. After all three rewrites, the
arithmetic closes automatically.
"

/-- The three boundary entries of row n+1 sum to n+3. -/
Statement (n : ℕ) : Nat.choose (n + 1) 1 + Nat.choose (n + 1) 0 + Nat.choose (n + 1) (n + 1) = n + 3 := by
  Hint "Apply the boundary theorems to simplify each `Nat.choose` term.
  Start with `Nat.choose_one_right` to simplify `Nat.choose (n + 1) 1`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]
  Hint "Good — the goal is now
  `(n + 1) + Nat.choose (n + 1) 0 + Nat.choose (n + 1) (n + 1) = n + 3`.
  Use `Nat.choose_zero_right` to simplify `Nat.choose (n + 1) 0`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]
  Hint "Almost there — the goal is
  `(n + 1) + 1 + Nat.choose (n + 1) (n + 1) = n + 3`.
  Use `Nat.choose_self` to simplify the last term."
  Hint (hidden := true) "Try `rw [Nat.choose_self]`."
  rw [Nat.choose_self]

Conclusion "
You simplified all three boundary values on a variable statement:

$$\\binom{n+1}{1} + \\binom{n+1}{0} + \\binom{n+1}{n+1} = (n+1) + 1 + 1 = n + 3$$

**The recipe**:
1. Identify which boundary theorem matches each `Nat.choose` term
2. Rewrite with `rw [Nat.choose_one_right]`, `rw [Nat.choose_zero_right]`,
   or `rw [Nat.choose_self]`
3. After all `Nat.choose` terms are eliminated, the arithmetic resolves

You can also combine all three rewrites into one:
`rw [Nat.choose_one_right, Nat.choose_zero_right, Nat.choose_self]`

This multi-step rewriting pattern is the core skill for the boss.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
