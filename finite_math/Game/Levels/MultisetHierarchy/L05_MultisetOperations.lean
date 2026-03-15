import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 5

Title "Multiset operations: map and card_map"

Introduction
"
# Operations on multisets

Multisets support many of the same operations as lists. In this level,
you will use two of them:

## `Multiset.map`

`Multiset.map f m` applies a function `f` to every element of the
multiset `m`, producing a new multiset. It works just like `List.map`,
but on multisets.

## `Multiset.card_map`

A key property is that **mapping preserves cardinality**:

```
Multiset.card_map : (Multiset.map f s).card = s.card
```

This makes sense: applying a function to each element does not add or
remove elements, only transforms them.

## Your task

Prove that mapping `(· + 10)` over the multiset `↑[1, 2, 3]` preserves
the cardinality (it is still 3).

**Strategy**: Use `rw [Multiset.card_map]` to eliminate the `map`, then
the goal becomes `Multiset.card (↑[1, 2, 3]) = 3`, which holds by `rfl`.

This is the **reduce-then-compute** pattern again: a structural lemma
simplifies the goal, then a basic tactic closes it.
"

/-- Mapping a function over a multiset preserves its cardinality. -/
Statement : Multiset.card (Multiset.map (· + 10) (↑([1, 2, 3] : List Nat) : Multiset Nat)) = 3 := by
  Hint "The goal involves `Multiset.card` applied to `Multiset.map`. You want to
  separate the `map` from the `card`. What lemma relates the cardinality of a
  mapped multiset to the cardinality of the original?"
  Hint (hidden := true) "Use `rw [Multiset.card_map]` to remove the `map` from
  the cardinality computation."
  rw [Multiset.card_map]
  Hint "Now the goal is `(↑[1, 2, 3] : Multiset Nat).card = 3`. The left side
  reduces to `List.length [1, 2, 3] = 3`, which is definitional. Try `rfl`."
  rfl

Conclusion
"
The lemma `Multiset.card_map` tells us that mapping a function over a
multiset does not change its size. This is the multiset analogue of the
list fact `(List.map f l).length = l.length`.

After rewriting with `Multiset.card_map`, the goal reduced to computing
the cardinality of `↑[1, 2, 3]`, which is `3` by definition.

**Key operations so far**:
- `Multiset.card m` -- number of elements (with multiplicity)
- `Multiset.map f m` -- apply `f` to each element
- `Multiset.card_map` -- mapping preserves cardinality
- `Multiset.mem_coe` -- membership is preserved under coercion
- `Multiset.coe_eq_coe` -- equality corresponds to permutation

**Foreshadowing**: Multisets also support `Multiset.filter` (analogous to
`List.filter` from W3). You will encounter it in a later world. There, you
will see that filtering can **change** cardinality (unlike mapping), because
it removes elements that do not satisfy the predicate.

**In plain language**: \"Transforming every element of a collection does
not change how many elements it has.\"
"

/-- `Multiset.map f m` applies the function `f` to every element of multiset `m`,
producing a new multiset. It is the multiset analogue of `List.map`.

For example, `Multiset.map (· + 10) ↑[1, 2, 3] = ↑[11, 12, 13]`. -/
DefinitionDoc Multiset.map as "Multiset.map"

/-- `Multiset.card_map` states that `(Multiset.map f s).card = s.card`.
Mapping a function over a multiset preserves cardinality because it transforms
elements without adding or removing any. -/
TheoremDoc Multiset.card_map as "Multiset.card_map" in "Multiset"

NewDefinition Multiset.map
NewTheorem Multiset.card_map
DisabledTactic trivial decide native_decide simp aesop simp_all
