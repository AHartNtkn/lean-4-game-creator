import Game.Metadata

World "BinomialCoefficients"
Level 4

Title "Computing with Pascal's Identity"

Introduction "
# Computing a Binomial Coefficient from Scratch

Pascal's identity lets you compute any binomial coefficient by
**expanding recursively** until you hit boundary values.

Let's compute $\\binom{4}{2} = 6$ by hand:
$$\\binom{4}{2} = \\binom{3}{1} + \\binom{3}{2}$$
$$= 3 + (\\binom{2}{1} + \\binom{2}{2})$$
$$= 3 + (2 + 1) = 6$$

Each step either:
- **Expands** using `choose_succ_succ` (Pascal's identity), or
- **Simplifies a leaf** using `choose_one_right` or `choose_self`

**Your task**: Prove $\\binom{4}{2} = 6$ using this recursive expansion.
"

/-- C(4, 2) = 6: computed by chaining Pascal's identity. -/
Statement : Nat.choose 4 2 = 6 := by
  Hint "Start by expanding C(4, 2) with Pascal's identity:
  C(4, 2) = C(3, 1) + C(3, 2)."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "The goal is `Nat.choose 3 1 + Nat.choose 3 2 = 6`.
  Simplify C(3, 1) = 3 using `choose_one_right`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]
  Hint "The goal is `3 + Nat.choose 3 2 = 6`.
  Expand C(3, 2) with Pascal's identity again."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "The goal is `3 + (Nat.choose 2 1 + Nat.choose 2 2) = 6`.
  Simplify the leaves: C(2, 1) = 2 and C(2, 2) = 1."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right, Nat.choose_self]`."
  rw [Nat.choose_one_right, Nat.choose_self]

Conclusion "
$\\binom{4}{2} = \\binom{3}{1} + \\binom{3}{2} = 3 + (2 + 1) = 6$

You just walked down **Pascal's triangle** by hand:
```
      1
     1 1
    1 2 1
   1 3 3 1
  1 4 [6] 4 1
```

The recipe for computing $\\binom{n}{k}$:
1. **Expand** interior entries with `choose_succ_succ` (Pascal's identity)
2. **Simplify leaves** with `choose_one_right` ($k = 1$) or `choose_self` ($k = n$)
3. Repeat until only numbers remain

This recursive expansion is exactly how Pascal's triangle is built
row by row. In the next level, you'll apply all three boundary
theorems on a **variable** statement.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
