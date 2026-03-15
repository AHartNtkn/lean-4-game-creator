import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 3

Title "Fintype.card equals Finset.univ.card"

Introduction
"
# The counting bridge: `Fintype.card`

You have seen `Finset.card` --- the cardinality of a specific finset.
Now meet `Fintype.card α` --- the number of elements in the *type* `α`.

## The definition

`Fintype.card α` is **defined** as `(Finset.univ : Finset α).card`.
In other words, the cardinality of a type is the cardinality of its
universal finset.

The lemma that states this relationship explicitly is:
```
Finset.card_univ : (Finset.univ : Finset α).card = Fintype.card α
```

## Your task

Prove this relationship for `Fin 5`: the cardinality of `Finset.univ`
for `Fin 5` equals `Fintype.card (Fin 5)`.

This is a direct application of `Finset.card_univ`. Use `exact` or `rw`.
"

/-- The cardinality of `Finset.univ` for `Fin 5` equals `Fintype.card (Fin 5)`. -/
Statement : (Finset.univ : Finset (Fin 5)).card = Fintype.card (Fin 5) := by
  Hint "The lemma `Finset.card_univ` says exactly this:
  `Finset.univ.card = Fintype.card α`. Try `exact Finset.card_univ`."
  Hint (hidden := true) "Use `exact Finset.card_univ`. Alternatively, since
  `Fintype.card` is *defined* as `Finset.univ.card`, `rfl` also works."
  exact Finset.card_univ

Conclusion
"
`Fintype.card` and `Finset.univ.card` are two names for the same number.
The lemma `Finset.card_univ` makes this bridge explicit.

## Why have both?

- `Finset.univ.card` is a *finset* operation: it takes a finset and counts
  its elements. You need to know which finset you are counting.
- `Fintype.card α` is a *type* operation: it takes a type and returns its
  size. It is cleaner for stating results like \"the number of elements
  of `Fin n` is `n`\".

Most cardinality theorems in mathlib are stated in terms of `Fintype.card`,
because it is more natural at the type level.

**In plain language**: \"The cardinality of a finite type is the number of
elements in its universal finset. These are two ways of saying the same thing.\"
"

/-- `Finset.card_univ` states that the cardinality of `Finset.univ`
equals `Fintype.card α`:
```
Finset.card_univ : (Finset.univ : Finset α).card = Fintype.card α
```

This bridges `Finset.card` (a finset operation) and `Fintype.card`
(a type-level operation).

**When to use**: When converting between `Finset.univ.card` and `Fintype.card`. -/
TheoremDoc Finset.card_univ as "Finset.card_univ" in "Fintype"

NewTheorem Finset.card_univ
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
