import Game.Metadata

World "Fintype"
Level 2

Title "Bool is Finite"

Introduction "
# Beyond Fin: Other Finite Types

`Fintype` isn't just for `Fin n`. Any type with finitely many elements
can have a `Fintype` instance. Lean's `Bool` type has exactly two values:
`true` and `false`.

The theorem `Fintype.card_bool` states:

$$\\text{Fintype.card Bool} = 2$$

**Your task**: Use `rw [Fintype.card_bool]` to prove that `Bool` has
exactly 2 elements. This follows the same `rw` pattern as L01.
"

/-- Bool has exactly 2 elements. -/
Statement : Fintype.card Bool = 2 := by
  Branch
    rfl
  Hint "Use `rw [Fintype.card_bool]` to rewrite the cardinality of
  `Bool` to `2`. The `rw` pattern is what you'll need going forward."
  rw [Fintype.card_bool]

Conclusion "
`Bool` has a `Fintype` instance with `card = 2`. Other familiar types
are also finite:

| Type | Card | Theorem |
|---|---|---|
| `Fin n` | `n` | `Fintype.card_fin` |
| `Bool` | `2` | `Fintype.card_bool` |
| `Unit` | `1` | `Fintype.card_unit` |

The real power of `Fintype` is that it's **compositional**: if `α` and
`β` are finite, then so are `α × β`, `α ⊕ β`, and even `α → β`. The
next levels teach the composition rules.
"

/-- `Fintype.card_bool` states that `Fintype.card Bool = 2`:
the type `Bool` has exactly two elements (`true` and `false`).

## Syntax
```
rw [Fintype.card_bool]      -- rewrites Fintype.card Bool to 2
exact Fintype.card_bool     -- proves Fintype.card Bool = 2
```
-/
TheoremDoc Fintype.card_bool as "Fintype.card_bool" in "Fintype"

/-- `Bool` is the type of boolean values: `true` and `false`.

It has exactly two elements, making it the simplest non-trivial
finite type.

## Values
- `true`
- `false`

## When you see it
`Bool` appears in type expressions like `Bool → α` (binary choices),
`Fin 2 → Bool` (binary strings), and `Fintype.card Bool = 2`.
-/
DefinitionDoc Bool as "Bool"

NewTheorem Fintype.card_bool
NewDefinition Bool

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
