import Game.Metadata

World "Finsupp"
Level 2

Title "Away from the Peak"

Introduction "
# Evaluating Away from the Support Point

You know that `Finsupp.single a b` evaluates to `b` at `a`. What
about at a *different* point `a'`?

The answer is `0` — the function is zero everywhere except at `a`.
The lemma is `Finsupp.single_eq_of_ne`:

```
Finsupp.single_eq_of_ne (h : a' ≠ a) : Finsupp.single a b a' = 0
```

Notice the argument order: `h` proves that the **evaluation point**
`a'` differs from the **support point** `a`.

**Your task**: Evaluate `Finsupp.single 3 7` at position `5`.
The result should be `0`.
"

/-- Evaluating a `single` away from its support point gives zero. -/
Statement : Finsupp.single 3 7 5 = 0 := by
  Hint "The evaluation point `5` differs from the support point `3`.
  Use `apply Finsupp.single_eq_of_ne` to reduce this to proving
  `5 ≠ 3`."
  Hint (hidden := true) "Try `apply Finsupp.single_eq_of_ne`. This
  leaves the goal `5 ≠ 3`."
  apply Finsupp.single_eq_of_ne
  Hint "Now prove `5 ≠ 3`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
`Finsupp.single a b` is nonzero at exactly one point. Everywhere
else, it returns `0`. Together, the two evaluation lemmas give you
complete control:

- **At the support point**: `Finsupp.single_eq_same` gives `b`
- **Away from it**: `Finsupp.single_eq_of_ne h` gives `0`

The side condition `a' ≠ a` in `single_eq_of_ne` is a natural
number inequality, so `omega` closes it.

**Pattern**: `apply Finsupp.single_eq_of_ne` then `omega`.
"

/-- `Finsupp.single_eq_of_ne` evaluates a single away from its
support point:

`Finsupp.single_eq_of_ne (h : a' ≠ a) : Finsupp.single a b a' = 0`

## Syntax
```
apply Finsupp.single_eq_of_ne    -- leaves `a' ≠ a` as goal
exact Finsupp.single_eq_of_ne h  -- when you have `h : a' ≠ a`
```

## When to use it
When the goal contains `Finsupp.single a b a'` where `a'` is
visibly different from `a`.

## Example
`apply Finsupp.single_eq_of_ne` on goal `Finsupp.single 3 7 5 = 0`
leaves `5 ≠ 3`, which `omega` closes.

## Warning
The inequality is `a' ≠ a` (evaluation point ≠ support point),
not the other way around.
-/
TheoremDoc Finsupp.single_eq_of_ne as "Finsupp.single_eq_of_ne" in "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.single_eq_of_ne

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
