import Game.Metadata

World "BinomialCoefficients"
Level 11

Title "Retrieval Practice"

Introduction "
# Retrieval Practice

You've learned six theorem families in rapid succession (Levels 6–10).
Before moving to induction, let's retrieve four of them on **variable**
statements:

**Part 1** — Symmetry (Level 6):
$\\binom{n+2}{n} = \\binom{n+2}{2}$

**Part 2** — Beyond the edge (Level 8):
$\\binom{n}{n+1} = 0$

**Part 3** — Factorial formula (Level 9):
$\\binom{n+3}{3} \\cdot 3! \\cdot n! = (n+3)!$

**Part 4** — Absorption identity (Level 10):
$(n+1) \\cdot \\binom{n}{3} = \\binom{n+1}{4} \\cdot 4$

Each part is one or two moves. Recall the patterns:
- Symmetry needs `have h : ... := by omega` then `exact Nat.choose_symm h`
- Beyond-edge and factorial use `apply ... ; omega`
- Absorption is a direct `rw`
"

/-- Retrieval practice: symmetry, beyond-the-edge, factorial formula, and absorption. -/
Statement (n : ℕ) :
    (Nat.choose (n + 2) n = Nat.choose (n + 2) 2) ∧
    (Nat.choose n (n + 1) = 0) ∧
    (Nat.choose (n + 3) 3 * Nat.factorial 3 * Nat.factorial n = Nat.factorial (n + 3)) ∧
    ((n + 1) * Nat.choose n 3 = Nat.choose (n + 1) 4 * 4) := by
  Hint "The goal is a 4-part conjunction. Split with `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  · Hint "**Part 1**: `Nat.choose (n + 2) n = Nat.choose (n + 2) 2`.
    Choosing n from n + 2 is the same as leaving out 2.
    Use symmetry: create a proof that `2 ≤ n + 2`, then apply
    `Nat.choose_symm`."
    Hint (hidden := true) "Try:
    `have h : 2 ≤ n + 2 := by omega`
    `exact Nat.choose_symm h`"
    have h : 2 ≤ n + 2 := by omega
    exact Nat.choose_symm h
  · Hint "Split the remaining conjunction with `constructor`."
    Hint (hidden := true) "Try `constructor`."
    constructor
    · Hint "**Part 2**: `Nat.choose n (n + 1) = 0`.
      You can't choose $n + 1$ items from $n$.
      Use `apply Nat.choose_eq_zero_of_lt`, then prove `n < n + 1`."
      Hint (hidden := true) "Try `apply Nat.choose_eq_zero_of_lt`."
      apply Nat.choose_eq_zero_of_lt
      Hint "The goal is `n < n + 1`. Use `omega`."
      Hint (hidden := true) "Try `omega`."
      omega
    · Hint "Split again with `constructor`."
      Hint (hidden := true) "Try `constructor`."
      constructor
      · Hint "**Part 3**: The factorial formula with `n + 3` and `k = 3`.
        Use `apply Nat.choose_mul_factorial_mul_factorial`, then prove `3 ≤ n + 3`."
        Hint (hidden := true) "Try `apply Nat.choose_mul_factorial_mul_factorial`."
        apply Nat.choose_mul_factorial_mul_factorial
        Hint "The goal is `3 ≤ n + 3`. Use `omega`."
        Hint (hidden := true) "Try `omega`."
        omega
      · Hint "**Part 4**: The absorption identity with k = 3:
        `(n + 1) * Nat.choose n 3 = Nat.choose (n + 1) 4 * 4`.
        Use `Nat.add_one_mul_choose_eq` to rewrite directly."
        Hint (hidden := true) "Try `rw [Nat.add_one_mul_choose_eq]`."
        rw [Nat.add_one_mul_choose_eq]

Conclusion "
You retrieved four theorem families on variable statements:

1. **Symmetry** (`choose_symm`): choosing $n$ from $n+2$ = choosing $2$ from $n+2$
2. **Beyond-edge** (`choose_eq_zero_of_lt`): choosing $n+1$ from $n$ gives $0$
3. **Factorial formula** (`choose_mul_factorial_mul_factorial`): connecting choose to factorials
4. **Absorption** (`add_one_mul_choose_eq`): the committee chair identity

**Patterns**:
- Symmetry: `have h : k ≤ n := by omega` + `exact Nat.choose_symm h`
- Beyond-edge: `apply choose_eq_zero_of_lt` + `omega`
- Factorial: `apply choose_mul_factorial_mul_factorial` + `omega`
- Absorption: direct `rw [add_one_mul_choose_eq]`

Next: coaching levels, a cross-world connection, and the boss.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
