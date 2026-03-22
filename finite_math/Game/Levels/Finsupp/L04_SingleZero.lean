import Game.Metadata

World "Finsupp"
Level 4

Title "When the Value is Zero"

Introduction "
# A Trap: Single with Value Zero

What happens if you create `Finsupp.single 3 0`? You might expect
a function with support containing `3`. But the value at `3` is `0`,
so actually `3` is NOT in the support — the function is zero
everywhere.

In fact, `Finsupp.single a 0` is exactly the zero finitely supported
function:

```
Finsupp.single_zero (a : α) : Finsupp.single a 0 = 0
```

Here, the `0` on the left is the value (a natural number), and
the `0` on the right is the zero element of `ℕ →₀ ℕ` — the
function that returns `0` at every input and has empty support.

**Your task**: Prove that `Finsupp.single 3 0` has empty support.
"

/-- A single with value zero has empty support. -/
Statement : (Finsupp.single 3 0 : ℕ →₀ ℕ).support = ∅ := by
  Hint "First, recognize that `Finsupp.single 3 0` IS the zero
  function. Rewrite with `Finsupp.single_zero` to replace it."
  Hint (hidden := true) "Try `rw [Finsupp.single_zero]`. This
  rewrites `Finsupp.single 3 0` to `0`, and the support of zero
  is empty by definition."
  rw [Finsupp.single_zero]
  Hint (hidden := true) "The support of the zero function is empty.
  Try `rfl` (it holds by definition) or `exact Finsupp.support_zero`."
  rfl

Conclusion "
This is an important edge case: `Finsupp.single a 0 = 0`. The
support of a `single` depends on whether the value is zero:

- `b ≠ 0`: support is the singleton containing `a`
  (`support_single_ne_zero`)
- `b = 0`: support is empty (`single_zero` + `support_zero`)

This is why `support_single_ne_zero` requires the side condition
`b ≠ 0` — without it, the claim would be false.

Note: the converse also holds. If `Finsupp.single a b = 0` then
`b = 0` (since the function is zero at every point, including `a`).
So `Finsupp.single a b = 0 ↔ b = 0` — the single is zero if and
only if the value is zero.

The lemma `Finsupp.support_zero : (0 : α →₀ M).support = ∅` names
the fact that the zero function has empty support. After
`rw [Finsupp.single_zero]` converted our single to `0`, the goal
`(0 : ℕ →₀ ℕ).support = ∅` held by definition (`rfl`).
"

/-- `Finsupp.single_zero` says that creating a single with value zero
gives the zero finitely supported function:

`Finsupp.single_zero (a : α) : Finsupp.single a 0 = 0`

## Syntax
```
rw [Finsupp.single_zero]
exact Finsupp.single_zero a
```

## When to use it
When `Finsupp.single a 0` appears in the goal. Rewriting replaces
it with `0 : α →₀ M`.

## Warning
The two `0`s in the statement mean different things: the `0` inside
`single` is the zero *value* (in `M`), while the `0` on the right
is the zero *function* (in `α →₀ M`).
-/
TheoremDoc Finsupp.single_zero as "Finsupp.single_zero" in "Finsupp"

/-- `Finsupp.support_zero` says the zero finitely supported function
has empty support:

`Finsupp.support_zero : (0 : α →₀ M).support = ∅`

## When to use it
After rewriting with `Finsupp.single_zero` to convert a single with
value zero to the zero function, this lemma (or `rfl`) closes the
resulting goal about the support being empty.
-/
TheoremDoc Finsupp.support_zero as "Finsupp.support_zero" in "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.single_zero Finsupp.support_zero

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
