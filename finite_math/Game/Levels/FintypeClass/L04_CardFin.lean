import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 4

Title "Fintype.card (Fin n) = n"

Introduction
"
# The fundamental count

The most basic cardinality fact for finite types is:
```
Fintype.card_fin : Fintype.card (Fin n) = n
```

This says: the type `Fin n` has exactly `n` elements.

## Your task

Prove `Fintype.card (Fin 7) = 7` using `Fintype.card_fin`.

You could close this with `rfl` (Lean can compute the cardinality), but
the pedagogical goal is to practice using `Fintype.card_fin` explicitly
with `rw` or `exact`.
"

/-- `Fin 7` has exactly 7 elements. -/
Statement : Fintype.card (Fin 7) = 7 := by
  Hint "Use the lemma `Fintype.card_fin`, which says `Fintype.card (Fin n) = n`.
  Try `rw [Fintype.card_fin]` or `exact Fintype.card_fin 7`."
  Hint (hidden := true) "Use `exact Fintype.card_fin 7`. This instantiates the
  lemma at `n = 7`."
  exact Fintype.card_fin 7

Conclusion
"
`Fintype.card_fin` is the foundational cardinality lemma for `Fin n`. It says
that `Fin n` has exactly `n` elements, which corresponds to the mathematical
fact that `{0, 1, ..., n-1}` has `n` elements.

## Building blocks

You now have three key tools:
1. `Finset.mem_univ` --- every element belongs to `Finset.univ`.
2. `Finset.card_univ` --- `Finset.univ.card = Fintype.card α`.
3. `Fintype.card_fin` --- `Fintype.card (Fin n) = n`.

These will combine with cardinality lemmas for compound types (products,
sums, function types) in the next levels.

**In plain language**: \"The set $\\{0, 1, \\ldots, n-1\\}$ has exactly $n$
elements.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
