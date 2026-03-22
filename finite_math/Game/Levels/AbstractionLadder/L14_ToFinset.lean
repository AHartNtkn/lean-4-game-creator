import Game.Metadata

World "AbstractionLadder"
Level 14

Title "List.toFinset"

Introduction "
# Climbing to the Top: List.toFinset

The function `List.toFinset` converts a list to a finset by removing
duplicates and forgetting order. The key membership lemma:

`List.mem_toFinset : a ∈ l.toFinset ↔ a ∈ l`

An element belongs to `l.toFinset` if and only if it appears somewhere
in `l`. The toFinset operation doesn't change *which* elements are
present — it only removes duplicate copies and forgets ordering.

There are also structural lemmas:
- `List.toFinset_nil : [].toFinset = ∅`
- `List.toFinset_cons : (a :: l).toFinset = insert a l.toFinset`

Notice how `toFinset_cons` mirrors the `insert`-based structure of
finsets: cons on lists becomes insert on finsets.

**Your task**: Prove that if `a` belongs to a list `l`, then `a`
belongs to `(b :: l).toFinset`. You'll need to unfold `toFinset_cons`,
use `Finset.mem_insert` from earlier worlds, and apply `mem_toFinset`.
"

/-- List membership carries through toFinset of a cons'd list. -/
Statement (a b : ℕ) (l : List ℕ) (h : a ∈ l) : a ∈ (b :: l).toFinset := by
  Hint "Start by unfolding `toFinset` of the cons'd list.
  Use `rw [List.toFinset_cons]` to get `a ∈ insert b l.toFinset`."
  rw [List.toFinset_cons]
  Hint "The goal is `a ∈ insert b l.toFinset`. This is the same
  `Finset.mem_insert` pattern from earlier worlds."
  rw [Finset.mem_insert]
  Hint "The goal is `a = b ∨ a ∈ l.toFinset`. Since we know `a ∈ l`,
  the right branch works."
  right
  Hint "Now prove `a ∈ l.toFinset` from `h : a ∈ l`."
  Hint (hidden := true) "Try `rw [List.mem_toFinset]` then `exact h`."
  rw [List.mem_toFinset]
  exact h

Conclusion "
You combined three tools:
1. `List.toFinset_cons` to unfold the toFinset of a cons'd list
2. `Finset.mem_insert` to handle the insert structure
3. `List.mem_toFinset` to bridge list and finset membership

This pattern shows the structural correspondence:
- **List**: `a :: l` (cons)
- **Finset**: `insert a l.toFinset`

The `toFinset_cons` lemma makes this correspondence explicit.

**Where this matters**: When you have data as a list (e.g., from a
computation) and need to reason about it as a finset (e.g., for
cardinality), `toFinset` is the bridge. The membership equivalence
means you don't lose any elements — you only lose structure.
"

/-- `List.toFinset l` converts a list to a finset, removing duplicates
and forgetting order.

## Key lemmas
- `List.mem_toFinset : a ∈ l.toFinset ↔ a ∈ l`
- `List.toFinset_nil : [].toFinset = ∅`
- `List.toFinset_cons : (a :: l).toFinset = insert a l.toFinset`
-/
DefinitionDoc List.toFinset as "List.toFinset"

/-- `List.mem_toFinset` states that
`a ∈ l.toFinset ↔ a ∈ l`.

Membership in `toFinset` is the same as membership in the list.

## Syntax
```
rw [List.mem_toFinset]
```

## When to use it
When converting between list membership and finset membership.
-/
TheoremDoc List.mem_toFinset as "List.mem_toFinset" in "List"

/-- `List.toFinset_cons` states that
`(a :: l).toFinset = insert a l.toFinset`.

## Syntax
```
rw [List.toFinset_cons]
```

## When to use it
When simplifying `toFinset` of a cons'd list.
-/
TheoremDoc List.toFinset_cons as "List.toFinset_cons" in "List"

TheoremTab "List"
NewDefinition List.toFinset
NewTheorem List.mem_toFinset List.toFinset_cons

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable List.mem_cons_of_mem
