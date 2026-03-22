import Game.Metadata

World "Fintype"
Level 1

Title "What is Fintype?"

Introduction "
# Fintype: The Typeclass of Finite Types

In the Cardinality world you used `Finset.card_univ` and `Fintype.card_fin`
to count elements. But what made those tools work? The answer is a
**typeclass** called `Fintype`.

`Fintype α` is Lean's way of saying: *the type `α` has finitely many
elements, and I know exactly what they all are.*

When `α` has a `Fintype` instance:
- `Finset.univ : Finset α` exists (the finset of ALL elements)
- `Fintype.card α : ℕ` is defined (the total count)

The simplest example: `Fin n` has a `Fintype` instance for every `n`.
The theorem `Fintype.card_fin n` says `Fintype.card (Fin n) = n`.

**Important warning**: Not every type is finite! The natural numbers `ℕ`
have **no** `Fintype` instance. Writing `Fintype.card ℕ` is a type error —
Lean will say it cannot find a `Fintype ℕ` instance. If you've only worked
with `Fin n`, this may be surprising: finiteness is a *property* that some
types have, not a universal given.

**Your task**: Use `Fintype.card_fin` to prove that `Fin n` has `n`
elements. The statement uses a variable `n`, so `rfl` won't work —
you must use `rw` to apply the lemma.
"

/-- `Fin n` has exactly `n` elements. -/
Statement (n : ℕ) : Fintype.card (Fin n) = n := by
  Hint "Use `rw [Fintype.card_fin]` to rewrite `Fintype.card (Fin n)`
  to `n`."
  rw [Fintype.card_fin]

Conclusion "
`Fintype.card_fin` is the bridge between the type `Fin n` and the
number `n`. Because the statement used a variable `n` (not a concrete
number like 7), `rfl` could not close the goal — you had to use `rw`
to apply the lemma. This `rw` pattern is the core technique for the
entire world.

| Tool | Type | What it says |
|---|---|---|
| `Fintype α` | typeclass | `α` has finitely many elements |
| `Fintype.card α` | `ℕ` | the number of elements of `α` |
| `Fintype.card_fin n` | equation | `Fintype.card (Fin n) = n` |

Next: `Fin n` isn't the only finite type. `Bool` is finite too.
"

/-- `Fintype α` is a typeclass that asserts the type `α` has finitely
many elements. When `α` has a `Fintype` instance, `Finset.univ : Finset α`
and `Fintype.card α : ℕ` are available.

## Key facts
- `Fintype.card α` counts the elements of `α`
- `Finset.univ` is the finset of all elements
- `Fintype.elems` is the underlying `Finset` in the `Fintype` instance
  (in practice, use `Finset.univ` — it's the user-facing API)
- Not every type is finite — `ℕ` has no `Fintype` instance

## Example
```
Fintype.card (Fin 5) = 5    -- via Fintype.card_fin
Fintype.card Bool = 2        -- Bool has two elements
```
-/
DefinitionDoc Fintype as "Fintype"

/-- `Fintype.card α` returns the number of elements of a finite type `α`.

## Syntax
```
Fintype.card α    -- where α has a Fintype instance
```

## When to use it
When you need to talk about how many elements a type has, rather than
how many elements a particular finset contains.

## Connection to Finset.card
- `Finset.card s` counts elements of a specific finset `s`
- `Fintype.card α` counts ALL elements of the type `α`
- They're connected: `Finset.card_univ : (Finset.univ).card = Fintype.card α`
-/
DefinitionDoc Fintype.card as "Fintype.card"

NewDefinition Fintype Fintype.card
NewTheorem Fintype.card_fin

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
