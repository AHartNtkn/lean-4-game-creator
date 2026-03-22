import Game.Metadata

World "Finsupp"
Level 1

Title "Evaluating a Single"

Introduction "
# What is a Finitely Supported Function?

A **finitely supported function** `f : α →₀ M` is a function from `α`
to `M` that equals zero at all but finitely many points. The type
`Finsupp α M` (notation `α →₀ M`) bundles together:
- the function itself
- a `Finset` called the **support**, recording where the function
  is nonzero
- a proof that these two agree

The simplest `Finsupp` is `Finsupp.single a b`: the function that
equals `b` at `a` and `0` everywhere else.

To evaluate `Finsupp.single a b` at the point `a` itself, use
`Finsupp.single_eq_same`:

```
Finsupp.single_eq_same : Finsupp.single a b a = b
```

This says: evaluating a single at its support point returns the value.

**Your task**: Evaluate `Finsupp.single 3 7` at position `3`.
"

/-- Evaluating a `single` at its support point returns the value. -/
Statement : Finsupp.single 3 7 3 = 7 := by
  Hint "Use `rw [Finsupp.single_eq_same]` to evaluate the function
  at position `3`."
  Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
  rw [Finsupp.single_eq_same]

Conclusion "
`Finsupp.single a b` is the fundamental building block of finitely
supported functions — a function with a single nonzero value `b` at
position `a`. The lemma `Finsupp.single_eq_same` evaluates it at
the support point.

**Pattern**: When you see `Finsupp.single a b a` in the goal, rewrite
with `Finsupp.single_eq_same` to replace it with `b`.

In the next level, you'll see what happens when you evaluate at a
*different* position.
"

/-- `Finsupp.single_eq_same` evaluates a single at its support point:

`Finsupp.single a b a = b`

## Syntax
```
rw [Finsupp.single_eq_same]
exact Finsupp.single_eq_same
```

## When to use it
When the goal contains `Finsupp.single a b a` — the evaluation point
matches the first argument of `single`.

## Example
`rw [Finsupp.single_eq_same]` turns `Finsupp.single 3 7 3 = 7`
into `7 = 7`.

## Warning
This only works when the evaluation point is *exactly* the same
as the first argument to `single`. If they differ, use
`Finsupp.single_eq_of_ne` instead.
-/
TheoremDoc Finsupp.single_eq_same as "Finsupp.single_eq_same" in "Finsupp"

/-- `Finsupp.single a b` is the finitely supported function that
has value `b` at `a` and `0` everywhere else.

## Syntax
```
Finsupp.single a b     -- a function with one nonzero value
```

## Type
If `a : α` and `b : M` where `M` has a zero, then
`Finsupp.single a b : α →₀ M`.

## Key lemmas
- `Finsupp.single_eq_same : Finsupp.single a b a = b`
- `Finsupp.single_eq_of_ne : a' ≠ a → Finsupp.single a b a' = 0`
- `Finsupp.support_single_ne_zero : b ≠ 0 → (Finsupp.single a b).support = singleton a`
-/
DefinitionDoc Finsupp.single as "Finsupp.single"

/-- `Finsupp α M` (notation: `α →₀ M`) is the type of finitely
supported functions from `α` to `M` — functions that are zero
everywhere except on a finite set called the **support**.

## Key definitions
- `Finsupp.single a b`: the function equal to `b` at `a`, `0` elsewhere
- `f.support`: the `Finset` where `f` is nonzero

## Key properties
- `Finsupp.mem_support_iff : a ∈ f.support ↔ f a ≠ 0`
- `Finsupp.add_apply : (f + g) a = f a + g a`
-/
DefinitionDoc Finsupp as "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.single_eq_same
NewDefinition Finsupp Finsupp.single

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
