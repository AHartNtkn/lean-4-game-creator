import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 5

Title "Bool as a Fintype"

Introduction
"
# `Fintype` beyond `Fin`

`Fin n` is not the only type with a `Fintype` instance. Lean provides
`Fintype` instances for many built-in types. One of the simplest is `Bool`.

`Bool` has exactly two elements: `true` and `false`. Lean automatically
provides a `Fintype Bool` instance, so `Finset.univ : Finset Bool = {true, false}`
and `Fintype.card Bool = 2`.

The key lemma is:
```
Fintype.card_bool : Fintype.card Bool = 2
```

## Your task

Prove that `Fintype.card Bool = 2`.

This is analogous to how you used `Fintype.card_fin` in the previous level.
"

/-- `Bool` has exactly 2 elements. -/
Statement : Fintype.card Bool = 2 := by
  Hint "The lemma `Fintype.card_bool` says `Fintype.card Bool = 2`.
  Try `exact Fintype.card_bool`."
  Hint (hidden := true) "Use `exact Fintype.card_bool`. Alternatively, `rfl` works
  since Lean can compute this."
  exact Fintype.card_bool

Conclusion
"
`Bool` is one of the simplest fintypes: it has exactly two elements.
The proof used `Fintype.card_bool`, which is a specialized lemma just
like `Fintype.card_fin` was for `Fin n`.

## The pattern

Every concrete type with a `Fintype` instance has a cardinality lemma:
- `Fintype.card_fin` for `Fin n`
- `Fintype.card_bool` for `Bool`
- `Fintype.card_prod` for product types (coming next)
- `Fintype.card_sum` for sum types
- and many more

The `Fintype` class is the common interface: once a type has the instance,
all the cardinality and enumeration machinery works automatically.

**In plain language**: \"There are exactly two boolean values: true and false.\"
"

/-- `Fintype.card_bool` states that `Bool` has exactly 2 elements:
```
Fintype.card_bool : Fintype.card Bool = 2
```

**When to use**: When computing the cardinality of `Bool` or a type
built from `Bool` (e.g., `Fin n × Bool`). -/
TheoremDoc Fintype.card_bool as "Fintype.card_bool" in "Fintype"

NewTheorem Fintype.card_bool
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
