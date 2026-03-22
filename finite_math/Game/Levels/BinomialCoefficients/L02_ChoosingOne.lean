import Game.Metadata

World "BinomialCoefficients"
Level 2

Title "Choosing One"

Introduction "
# Choosing One Element

How many ways can you choose 1 item from a set of $n$ items?

Exactly $n$ ways — you pick any one of the $n$ items. This gives us:

$$\\binom{n}{1} = n$$

In Lean: `Nat.choose_one_right : Nat.choose n 1 = n`

**Your task**: Verify this for $n = 7$.
"

/-- `Nat.choose_one_right` states that `Nat.choose n 1 = n`.

## Syntax
```
rw [Nat.choose_one_right]
```

## When to use it
When you see `Nat.choose n 1` in the goal or a hypothesis and
want to simplify it to `n`.

## Meaning
There are exactly `n` ways to choose 1 item from `n` items.
-/
TheoremDoc Nat.choose_one_right as "Nat.choose_one_right" in "Choose"

/-- C(7, 1) = 7: there are 7 ways to choose 1 item from 7. -/
Statement : Nat.choose 7 1 = 7 := by
  Hint "There are $n$ ways to choose 1 from $n$.
  Use `Nat.choose_one_right`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]

Conclusion "
$\\binom{n}{1} = n$ — choosing one is just picking any element.

Together with the boundary values:
- $\\binom{n}{0} = 1$ (choose nothing)
- $\\binom{n}{1} = n$ (choose one)
- $\\binom{n}{n} = 1$ (choose everything)

These three formulas handle the simplest cases. For
$2 \\le k \\le n - 1$, we need **Pascal's identity** — coming up next.
"

NewTheorem Nat.choose_one_right

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
