import Game.Metadata

World "BinomialCoefficients"
Level 9

Title "The Factorial Connection"

Introduction "
# The Factorial Formula

The binomial coefficient connects to the factorial through:

$$\\binom{n}{k} \\cdot k! \\cdot (n-k)! = n!$$

Or equivalently: $\\binom{n}{k} = \\frac{n!}{k! \\cdot (n-k)!}$

**Why is this true?** There are $n!$ ways to arrange $n$ objects in a line.
Choosing $k$ of them (in $\\binom{n}{k}$ ways), then arranging the
chosen $k$ objects ($k!$ ways) and the remaining $n-k$ objects
($(n-k)!$ ways), accounts for every arrangement exactly once.

The multiplicative form avoids division and is more natural for proofs:
```
Nat.choose_mul_factorial_mul_factorial :
  k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n
```

**Your task**: Verify the multiplicative formula for $n = 5, k = 2$:
$\\binom{5}{2} \\cdot 2! \\cdot 3! = 5!$
"

/-- `Nat.choose_mul_factorial_mul_factorial` states that
`Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n`
when `k ≤ n`.

## Syntax
```
apply Nat.choose_mul_factorial_mul_factorial
omega
```
or equivalently:
```
exact Nat.choose_mul_factorial_mul_factorial (by omega)
```

## When to use it
When you need to connect binomial coefficients to factorials in a
multiplication context. This avoids the integer division in the
formula $\binom{n}{k} = n! / (k!(n-k)!)$.

-/
TheoremDoc Nat.choose_mul_factorial_mul_factorial as "Nat.choose_mul_factorial_mul_factorial" in "Choose"

/-- The factorial formula: C(5,2) * 2! * 3! = 5!. -/
Statement : Nat.choose 5 2 * Nat.factorial 2 * Nat.factorial (5 - 2) = Nat.factorial 5 := by
  Hint "This is an instance of the factorial formula:
  C(n, k) * k! * (n - k)! = n!

  Use `apply Nat.choose_mul_factorial_mul_factorial` to apply the
  theorem, leaving the inequality `2 ≤ 5` as a subgoal."
  Hint (hidden := true) "Try `apply Nat.choose_mul_factorial_mul_factorial`."
  apply Nat.choose_mul_factorial_mul_factorial
  Hint "The goal is `2 ≤ 5`. Use `omega` to close it."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
$\\binom{5}{2} \\cdot 2! \\cdot 3! = 10 \\cdot 2 \\cdot 6 = 120 = 5!$

The factorial formula is the **closed form** for binomial coefficients.
While Pascal's identity gives a recursive way to compute $\\binom{n}{k}$,
the factorial formula gives a direct computation:

$$\\binom{5}{2} = \\frac{5!}{2! \\cdot 3!} = \\frac{120}{2 \\cdot 6} = 10$$

In proofs, the **multiplicative form** is usually more convenient than
the division form, because natural number division rounds down and
can lose information. The multiplicative form
$\\binom{n}{k} \\cdot k! \\cdot (n-k)! = n!$
avoids this issue entirely.

You now have the full toolkit. These tools aren't just abstract —
they're the building blocks for the **binomial theorem**:
$(x+y)^n = \\sum_k \\binom{n}{k} x^k y^{n-k}$, which you'll prove
in a later world. And the **Powerset** world will ground $\\binom{n}{k}$
as literally counting $k$-element subsets of a Finset.

Next: the **absorption identity**, which shows the factorial formula
in action as a tool for deriving new identities.
"

NewTheorem Nat.choose_mul_factorial_mul_factorial

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
