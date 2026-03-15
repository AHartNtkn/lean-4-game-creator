import GameServer.Commands
import Mathlib

World "ListBasics"
Level 5

Title "Map preserves membership"

Introduction
"
# Applying a function to every element

`List.map f l` applies the function `f` to every element of `l`, producing
a new list of the same length.

For example:
- `List.map (· + 10) [1, 2, 3] = [11, 12, 13]`
- `List.map (· * 2) [5, 10] = [10, 20]`

## Map preserves membership

If `a` is in `l`, then `f a` is in `List.map f l`. This is the key
property that connects list membership before and after mapping.

The lemma you need is `List.mem_map`:
```
List.mem_map : b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
```

This says: `b` is in the mapped list if and only if there exists some
element `a` in the original list such that `f a = b`.

(Note: `∃ a ∈ l, f a = b` is notation for `∃ a, a ∈ l ∧ f a = b`.)

## Your task

Given `h : a ∈ l`, prove that `f a ∈ List.map f l`.

**Strategy**:
1. `rw [List.mem_map]` to unfold what it means to be in the mapped list
2. `exact ⟨a, h, rfl⟩` to provide the witness `a`, the membership proof `h`,
   and the equality `f a = f a` by `rfl`, all at once

Or, for a more step-by-step approach:
1. `rw [List.mem_map]`
2. `refine ⟨a, h, ?_⟩` to provide the witness and membership, leaving the equality
3. `rfl` to close the equality
"

/-- If `a ∈ l`, then `f a ∈ List.map f l`. -/
Statement (f : Nat → Nat) (a : Nat) (l : List Nat) (h : a ∈ l) :
    f a ∈ List.map f l := by
  Hint "The goal is `f a ∈ List.map f l`. Unfold the membership
  characterization with `rw [List.mem_map]`."
  rw [List.mem_map]
  Hint "The goal is now `∃ a_1 ∈ l, f a_1 = f a`. You need to provide
  a witness and verify the conditions.

  Try `refine ⟨a, h, ?_⟩` to provide the witness `a` and membership `h`,
  leaving only the equality to prove.

  Or close everything at once with `exact ⟨a, h, rfl⟩`."
  refine ⟨a, h, ?_⟩
  Hint "The goal is `f a = f a`. Close with `rfl`."
  rfl

DisabledTactic decide native_decide simp aesop

Conclusion
"
You proved that mapping preserves membership: if `a` is in `l`, then
`f a` is in `List.map f l`. The proof had a natural structure:

1. Unfold what \"in the mapped list\" means: there exists a preimage
2. Provide the witness: `a` itself, together with `h : a ∈ l`
3. Verify the equality: `f a = f a` by reflexivity

This is an existential proof. The `refine ⟨witness, proof, ?_⟩` pattern
is useful when you want to provide some parts and leave others as subgoals.

**Key properties of `List.map`**:
- `List.map f [] = []`
- `List.map f (a :: l) = f a :: List.map f l`
- `(List.map f l).length = l.length` (map preserves length)
- `b ∈ List.map f l ↔ ∃ a ∈ l, f a = b`

**In plain language**: \"If an element appears in a list, then its image
under $f$ appears in the list obtained by applying $f$ to every element.\"

This will reappear when we study `Finset.image` -- the finset analogue
of mapping a function over a collection.
"

/-- `List.map f l` applies the function `f` to every element of `l`,
producing a new list of the same length.
- `List.map f [] = []`
- `List.map f (a :: l) = f a :: List.map f l`
- `(List.map f l).length = l.length` -/
DefinitionDoc List.map as "List.map"

/-- `List.mem_map` states that `b ∈ List.map f l ↔ ∃ a ∈ l, f a = b`.
An element is in the mapped list iff it has a preimage in the original list. -/
TheoremDoc List.mem_map as "List.mem_map" in "List"

/-- `refine e` is like `exact e`, but allows you to leave holes (written `?_`)
in the expression. Each hole becomes a new subgoal. This lets you provide
partial proofs and fill in the remaining pieces step by step.

Example: `refine ⟨a, h, ?_⟩` provides the first two components of an
anonymous constructor and leaves the third as a subgoal. -/
TacticDoc refine

NewDefinition List.map
NewTheorem List.mem_map
NewTactic refine
