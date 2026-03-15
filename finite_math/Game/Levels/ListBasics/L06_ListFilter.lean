import GameServer.Commands
import Mathlib

World "ListBasics"
Level 6

Title "Filtering a list"

Introduction
"
# Selecting elements with `List.filter`

`List.filter p l` keeps only those elements of `l` that satisfy the
predicate `p`, discarding the rest. The relative order of kept elements
is preserved.

For example (thinking of `p` as \"less than 4\"):
- Filtering `[1, 4, 2, 5, 3]` keeps `[1, 2, 3]`
- Filtering `[10, 20]` keeps `[]`

## Membership in a filtered list

The key lemma about membership in filtered lists is `List.mem_filter`:
```
List.mem_filter : a ∈ List.filter p l ↔ a ∈ l ∧ p a = true
```

An element is in the filtered list if and only if it was in the original
list **and** it satisfies the predicate.

## Your task

Given that `a ∈ l` and that `p a = true`, prove that `a ∈ List.filter p l`.

**Strategy**:
1. `rw [List.mem_filter]` to unfold the membership condition
2. `constructor` to split the conjunction
3. Close each side with `exact`
"

/-- If `a ∈ l` and `p a = true`, then `a ∈ List.filter p l`. -/
Statement (p : Nat → Bool) (a : Nat) (l : List Nat)
    (hmem : a ∈ l) (hpred : p a = true) :
    a ∈ List.filter p l := by
  Hint "The goal is `a ∈ List.filter p l`. Unfold the membership condition
  with `rw [List.mem_filter]`."
  rw [List.mem_filter]
  Hint "The goal is now `a ∈ l ∧ p a = true`. Split it with `constructor`."
  constructor
  Hint "Two subgoals: `a ∈ l` and `p a = true`. Close each with `exact`."
  · exact hmem
  · exact hpred

DisabledTactic decide native_decide simp aesop

Conclusion
"
You proved that an element satisfying the predicate stays in the filtered
list. The proof had the same conjunction-splitting pattern as the map level.

Notice that the predicate `p` has type `Nat → Bool` -- it returns `true`
or `false` for each element. This is why the condition is `p a = true`
rather than a `Prop`-valued statement. In Lean 4, `List.filter` uses
`Bool`-valued predicates.

**Key observations about filtering**:
- **Filtering can only shrink or preserve a list** -- never grow it.
  So `(List.filter p l).length ≤ l.length`.
- **Filtering preserves order** -- the kept elements appear in the same
  relative order as in the original list.

**In plain language**: \"Remove all elements that don't satisfy the
condition, keeping the rest in their original order.\"

When we study `Finset.filter` later, you will see the same idea applied
to finite sets rather than lists.
"

/-- `List.filter p l` keeps only those elements `a` of `l` for which
`p a = true`, preserving their relative order.
- `List.filter p [] = []`
- Filtering can only shrink or preserve a list
- `a ∈ List.filter p l ↔ a ∈ l ∧ p a = true` -/
DefinitionDoc List.filter as "List.filter"

/-- `List.mem_filter` states that `a ∈ List.filter p l ↔ a ∈ l ∧ p a = true`.
An element is in the filtered list iff it was in the original list and satisfies
the predicate. -/
TheoremDoc List.mem_filter as "List.mem_filter" in "List"

NewDefinition List.filter
NewTheorem List.mem_filter
