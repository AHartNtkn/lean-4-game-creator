import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 2

Title "Finset.univ contains all elements"

Introduction
"
# The universal property of `Finset.univ`

The defining property of `Finset.univ` is that *every* element of the
type belongs to it. This is the lemma:
```
Finset.mem_univ : ∀ (x : α), x ∈ (Finset.univ : Finset α)
```

This lemma requires `[Fintype α]` --- Lean must know the type is finite
in order to have a universal finset.

## Your task

Let `x` be an arbitrary element of `Fin 3`. Prove that `x` belongs to
`Finset.univ`.

Start with `intro` to name the element, then apply the right lemma.
"

/-- Every element of `Fin 3` belongs to `Finset.univ`. -/
Statement : ∀ x : Fin 3, x ∈ (Finset.univ : Finset (Fin 3)) := by
  Hint "Start by introducing the arbitrary element: `intro x`."
  intro x
  Hint "Now you need to show `x ∈ Finset.univ`. The lemma `Finset.mem_univ`
  says exactly this for any element of a `Fintype`. Try `exact Finset.mem_univ x`."
  Hint (hidden := true) "Use `exact Finset.mem_univ x`."
  exact Finset.mem_univ x

Conclusion
"
The proof was a direct application of `Finset.mem_univ`. This lemma is the
formal statement of universality: if `α` has a `Fintype` instance, then
every `x : α` belongs to `Finset.univ`.

## Contrast with ordinary finsets

In earlier worlds, membership in a finset required *proof*. For example,
to show `3 ∈ {1, 2, 3}`, you needed to rewrite with `Finset.mem_insert`.
But `Finset.univ` is special: membership is *automatic*. This is the
power of the `Fintype` class --- it guarantees that no element is missing.

**In plain language**: \"If a type is finite, then every element of
that type appears in the universal finset. There are no missing elements.\"
"

/-- `Finset.mem_univ` states that every element of a `Fintype` belongs
to `Finset.univ`:
```
Finset.mem_univ : ∀ (x : α), x ∈ Finset.univ
```
(requires `[Fintype α]`)

**When to use**: Whenever you need `x ∈ Finset.univ`. This is the
most basic fact about the universal finset. -/
TheoremDoc Finset.mem_univ as "Finset.mem_univ" in "Fintype"

NewTheorem Finset.mem_univ
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
