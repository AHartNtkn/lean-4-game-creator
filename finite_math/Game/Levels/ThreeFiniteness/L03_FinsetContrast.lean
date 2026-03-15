import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 3

Title "Finset: A concrete finite collection"

Introduction
"
# `Finset` vs `Set.Finite` vs `Fintype`

You now know two notions of finiteness:
- `Set.Finite s` — a predicate saying a set is finite.
- `Fintype α` — a type class saying a type is finite.

The third notion is `Finset α`, which you have been using since early in
this course. A `Finset` is not a predicate or a type class — it is a
**data structure**: a concrete, computable collection of distinct elements.

## Comparison

| | `Set.Finite s` | `Fintype α` | `Finset α` |
|---|---|---|---|
| **What is it** | Predicate | Type class | Data type |
| **Lives in** | `Prop` | instance system | a term |
| **Data** | none | `Finset.univ` | the elements themselves |
| **Computable** | no | partially | yes |

## The bridge: `Finset.finite_toSet`

Every `Finset` can be coerced to a `Set`. Since a `Finset` has finitely
many elements by construction, this coerced set is always finite:

```
Finset.finite_toSet : (s : Finset α) → (↑s : Set α).Finite
```

This bridges `Finset` back to `Set.Finite`: if you have a concrete
finset, its underlying set is automatically `Set.Finite`.

## Your task

Prove that the coercion of the finset `{1, 2, 3}` to a set is `Set.Finite`.
"

/-- The coercion of the finset `{1, 2, 3}` to a set is finite. -/
Statement : (↑({1, 2, 3} : Finset Nat) : Set Nat).Finite := by
  Hint "A finset is finite by construction. The lemma `Finset.finite_toSet`
  proves that the coercion of any finset to a set is `Set.Finite`.
  Try `exact Finset.finite_toSet _`."
  Hint (hidden := true) "Use `exact Finset.finite_toSet _`.
  The underscore lets Lean infer which finset you mean."
  exact Finset.finite_toSet _

Conclusion
"
You proved that the set underlying a finset is `Set.Finite`, using the
lemma `Finset.finite_toSet`.

## The three notions, summarized

You have now seen all three notions of finiteness:

1. **`Set.Finite s`**: \"This set is finite.\" A proof obligation, no data.
2. **`Fintype α`**: \"This type is finite.\" Comes with `Finset.univ`.
3. **`Finset α`**: \"Here are the elements.\" A concrete collection.

And you know two bridges:
- `Set.finite_univ` : `Fintype α → (Set.univ : Set α).Finite`
- `Finset.finite_toSet` : `Finset α → Set.Finite`

In the next level, you will learn to go the *other direction*: from
`Set.Finite` to `Finset`, using `Set.Finite.toFinset`.

**In plain language**: \"A finset literally lists its elements, so it is
finite by construction. The other two notions require proof.\"
"

/-- `Finset.finite_toSet s` proves that the coercion of a finset `s` to
a set is `Set.Finite`. Since a finset has finitely many elements by
construction, this is always true.

**Type**: `Finset.finite_toSet (s : Finset α) : (↑s : Set α).Finite`

**When to use**: When you have a `Finset` and need a `Set.Finite` proof
for its underlying set. -/
TheoremDoc Finset.finite_toSet as "Finset.finite_toSet" in "Finset"

NewTheorem Finset.finite_toSet
DisabledTactic trivial decide native_decide simp aesop simp_all
