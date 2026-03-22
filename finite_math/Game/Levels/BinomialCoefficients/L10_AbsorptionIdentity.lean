import Game.Metadata

World "BinomialCoefficients"
Level 10

Title "The Absorption Identity"

Introduction "
# The Absorption Identity

The factorial formula from Level 8 isn't just a curiosity — it
implies one of the most important binomial coefficient identities:

$$(n + 1) \\cdot \\binom{n}{k} = (k + 1) \\cdot \\binom{n+1}{k+1}$$

This is the **absorption identity**. It has a beautiful combinatorial
interpretation called the **committee chair** argument:

- **Right side**: Choose a $(k+1)$-member committee from $n+1$ people,
  then pick one of the $k+1$ members to be chair.
- **Left side**: Pick the chair first ($(n+1)$ choices), then choose
  the remaining $k$ committee members from the other $n$ people.

Both sides count the same thing — the number of ways to form a
committee with a designated chair — so they must be equal.

In Lean, this is `Nat.add_one_mul_choose_eq`:
```
Nat.add_one_mul_choose_eq :
  (n + 1) * Nat.choose n k = Nat.choose (n + 1) (k + 1) * (k + 1)
```

**Your task**: Apply the absorption identity for $k = 2$.
"

/-- `Nat.add_one_mul_choose_eq` states that
`(n + 1) * Nat.choose n k = Nat.choose (n + 1) (k + 1) * (k + 1)`.

This is the **absorption identity**. It connects adjacent entries
in Pascal's triangle through multiplication.

## Syntax
```
rw [Nat.add_one_mul_choose_eq]
```

## Combinatorial meaning
Choosing a $(k+1)$-member committee from $n+1$ people and then
picking a chair (right side) equals picking the chair first from
$n+1$ people and then choosing the remaining $k$ members (left side).

## Related
This can be derived from the factorial formula
`choose_mul_factorial_mul_factorial`.
-/
TheoremDoc Nat.add_one_mul_choose_eq as "Nat.add_one_mul_choose_eq" in "Choose"

/-- The absorption identity for k = 2:
(n + 1) * C(n, 2) = C(n + 1, 3) * 3. -/
Statement (n : ℕ) : (n + 1) * Nat.choose n 2 = Nat.choose (n + 1) 3 * 3 := by
  Hint "This is a direct instance of the absorption identity with $k = 2$.
  Use `Nat.add_one_mul_choose_eq` to rewrite the left side."
  Hint (hidden := true) "Try `rw [Nat.add_one_mul_choose_eq]`."
  rw [Nat.add_one_mul_choose_eq]

Conclusion "
The absorption identity connects adjacent entries of Pascal's
triangle through multiplication:
$$(n + 1) \\cdot \\binom{n}{k} = (k + 1) \\cdot \\binom{n+1}{k+1}$$

The **committee chair** argument gives a beautiful proof without
any algebra: both sides count the same thing (committees with a
designated chair), just in different order.

This pattern — counting the same set in two ways to prove an
identity — is called **double counting**. It is one of the most
powerful techniques in combinatorics.

The absorption identity also shows the factorial formula *in action*:
it's equivalent to canceling $k!$ from both sides of
$\\binom{n}{k} \\cdot k! = \\frac{n!}{(n-k)!}$. The factorial formula
(Level 8) is a *tool*, not just a formula.
"

NewTheorem Nat.add_one_mul_choose_eq

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
