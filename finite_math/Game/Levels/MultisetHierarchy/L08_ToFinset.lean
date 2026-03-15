import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 8

Title "From Multiset to Finset: toFinset"

Introduction
"
# Dropping multiplicity with `toFinset`

You have seen that a multiset remembers how many times each element
appears. The next step in the hierarchy is to forget this multiplicity
information, producing a **finset** -- a finite set with no duplicates.

## `Multiset.toFinset`

The function `Multiset.toFinset` converts a multiset to a finset by
removing duplicate elements:

```
Multiset.toFinset : Multiset α → Finset α
```

For example, the multiset `↑[1, 2, 1, 3]` has four elements (with
`1` appearing twice). Converting to a finset with `toFinset` gives
`{1, 2, 3}` -- a set with three elements, each appearing exactly once.

## Your task

Prove that converting the multiset `↑[1, 2, 1, 3]` to a finset
gives `{1, 2, 3}`.
"

/-- Converting the multiset `↑[1, 2, 1, 3]` to a finset gives `{1, 2, 3}`. -/
Statement : Multiset.toFinset (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = {1, 2, 3} := by
  Hint "The goal is a concrete equality: does `toFinset` of this specific multiset
  equal this specific finset? Both sides can be evaluated. What tactic evaluates
  concrete decidable propositions?"
  Hint (hidden := true) "Try `decide`. It can evaluate `toFinset` on a concrete
  multiset and compare the result to a concrete finset."
  decide

Conclusion
"
The conversion `Multiset.toFinset` removes duplicates: the multiset
`↑[1, 2, 1, 3]` had two copies of `1`, but the finset `{1, 2, 3}`
contains each element at most once.

This is the second step in the hierarchy:
1. `List → Multiset`: forget **order** (via `↑`)
2. `Multiset → Finset`: forget **multiplicity** (via `toFinset`)

Notice that information is lost at each step:
- After step 1, you can no longer tell whether `1` came before or after `2`
- After step 2, you can no longer tell that `1` appeared twice

**In plain language**: \"Converting a bag to a set means keeping only the
distinct items and forgetting how many copies of each you had.\"
"

/-- `Multiset.toFinset m` converts multiset `m` to a finset by removing
duplicate elements. Each element that appeared one or more times in the
multiset appears exactly once in the resulting finset.

For example, `Multiset.toFinset ↑[1, 2, 1, 3] = {1, 2, 3}`. -/
DefinitionDoc Multiset.toFinset as "Multiset.toFinset"

NewDefinition Multiset.toFinset
DisabledTactic trivial native_decide simp aesop simp_all
