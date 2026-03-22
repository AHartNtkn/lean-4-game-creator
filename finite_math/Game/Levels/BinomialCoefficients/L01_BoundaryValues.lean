import Game.Metadata

World "BinomialCoefficients"
Level 1

Title "Boundary Values"

Introduction "
# Meet the Binomial Coefficient

The **binomial coefficient** $\\binom{n}{k}$, written `Nat.choose n k` in Lean,
counts the number of ways to choose $k$ items from a collection of $n$ items
(without regard to order). See the `Nat.choose` entry in the inventory panel
for the full recursive definition.

The two most important base cases are the **boundary values**:
- $\\binom{n}{0} = 1$ — choosing nothing: one way (take nothing)
- $\\binom{n}{n} = 1$ — choosing everything: one way (take all)

**Your task**: Prove both boundary values for $n = 5$:
- $\\binom{5}{0} = 1$ using `Nat.choose_zero_right`
- $\\binom{5}{5} = 1$ using `Nat.choose_self`
"

/-- `Nat.choose n k` (also written $\binom{n}{k}$ or $C(n, k)$) is the
number of ways to choose `k` items from `n` items without regard to order.

## Definition (recursive)
- `Nat.choose n 0 = 1`
- `Nat.choose 0 (k + 1) = 0`
- `Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)`

## Key boundary values
- `Nat.choose_zero_right : Nat.choose n 0 = 1`
- `Nat.choose_self : Nat.choose n n = 1`

## Combinatorial meaning
`Nat.choose n k` counts the `k`-element subsets of an `n`-element set.
-/
DefinitionDoc Nat.choose as "Nat.choose"

/-- `Nat.choose_zero_right` states that `Nat.choose n 0 = 1`.

## Syntax
```
rw [Nat.choose_zero_right]
```

## When to use it
When you see `Nat.choose n 0` in the goal or a hypothesis and want
to simplify it to `1`.

## Meaning
There is exactly one way to choose zero items from any collection:
take nothing.
-/
TheoremDoc Nat.choose_zero_right as "Nat.choose_zero_right" in "Choose"

/-- `Nat.choose_self` states that `Nat.choose n n = 1`.

## Syntax
```
rw [Nat.choose_self]
```

## When to use it
When you see `Nat.choose n n` in the goal or a hypothesis and want
to simplify it to `1`.

## Meaning
There is exactly one way to choose all items from a collection:
take everything.
-/
TheoremDoc Nat.choose_self as "Nat.choose_self" in "Choose"

/-- The boundary values: C(5,0) = 1 and C(5,5) = 1. -/
Statement : Nat.choose 5 0 = 1 ∧ Nat.choose 5 5 = 1 := by
  Hint "The goal is a conjunction `P ∧ Q`. Split it with `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  · Hint "**Left goal**: `Nat.choose 5 0 = 1`.
    Choosing zero items from any collection gives 1.
    Use `Nat.choose_zero_right` to rewrite."
    Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
    rw [Nat.choose_zero_right]
  · Hint "**Right goal**: `Nat.choose 5 5 = 1`.
    Choosing all items from a collection gives 1.
    Use `Nat.choose_self` to rewrite."
    Hint (hidden := true) "Try `rw [Nat.choose_self]`."
    rw [Nat.choose_self]

Conclusion "
You proved the two boundary values of `Nat.choose`:

- $\\binom{n}{0} = 1$ — choosing nothing: one way (take nothing)
- $\\binom{n}{n} = 1$ — choosing everything: one way (take all)

These are the **base cases** of Pascal's triangle. Every row starts
and ends with $1$.

**Reusable recipe**: When you see `Nat.choose n 0` or `Nat.choose n n`
in a goal, rewrite with `choose_zero_right` or `choose_self`.
"

/-- Disabled: gives a direct formula for choose (n+1) n that bypasses induction. -/
TheoremDoc Nat.choose_succ_self_right as "Nat.choose_succ_self_right" in "Choose"

/-- Disabled: characterizes when choose n k = 1, bypassing intended proof paths. -/
TheoremDoc Nat.choose_eq_one_iff as "Nat.choose_eq_one_iff" in "Choose"

NewTheorem Nat.choose_zero_right Nat.choose_self
NewDefinition Nat.choose

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
