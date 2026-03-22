import Game.Metadata

World "AbstractionLadder"
Level 15

Title "Multiset.toFinset"

Introduction "
# The Middle-to-Top Bridge: Multiset.toFinset

You've seen `List.toFinset` — the direct list-to-finset conversion.
But the abstraction ladder has a middle layer too: `Multiset`.

The function `Multiset.toFinset` converts a multiset to a finset
by removing duplicates. The key membership lemma:

`Multiset.mem_toFinset : a ∈ m.toFinset ↔ a ∈ m`

This is the multiset analogue of `List.mem_toFinset`. An element
belongs to `m.toFinset` if and only if it appears in `m`.

The full path up the ladder:
```
List α  →  Multiset α  →  Finset α
       ↑l            .toFinset
```

**Your task**: Given `h : a ∈ m` for a multiset `m`, prove
`a ∈ m.toFinset`.
"

/-- Multiset membership implies toFinset membership. -/
Statement (a : ℕ) (m : Multiset ℕ) (h : a ∈ m) : a ∈ m.toFinset := by
  Hint "The bridge lemma `Multiset.mem_toFinset` converts between
  multiset membership and finset membership.
  Use `rw [Multiset.mem_toFinset]` to convert the goal."
  rw [Multiset.mem_toFinset]
  Hint "The goal is now `a ∈ m`. You have `h : a ∈ m`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`Multiset.mem_toFinset` works exactly like `List.mem_toFinset`:
membership is preserved, but duplicates are forgotten.

The two toFinset functions correspond to the two arrows in the
abstraction ladder:
- `List.toFinset` climbs from bottom to top in one step
- `Multiset.toFinset` climbs from middle to top

Internally, `List.toFinset l = (↑l : Multiset α).toFinset` — the
list-to-finset conversion goes through the multiset layer.

**Going back down**: You can also descend the ladder. Every `Finset`
stores its elements as a `Multiset` internally, accessible via
`Finset.val`. So `s.val` gives the underlying `Multiset` of a
finset `s`. You won't need to use `Finset.val` directly in this
world, but knowing it exists helps understand the internal structure.

**The complete bridge toolkit**:
| Bridge | Lemma |
|---|---|
| List → Multiset | `Multiset.coe_eq_coe`, `Multiset.mem_coe` |
| Multiset → Finset | `Multiset.mem_toFinset` |
| List → Finset | `List.mem_toFinset`, `List.toFinset_cons` |
| Finset → Multiset | `Finset.val` (the underlying multiset) |
"

/-- `Multiset.toFinset m` converts a multiset to a finset by removing
duplicates.

## Key lemma
- `Multiset.mem_toFinset : a ∈ m.toFinset ↔ a ∈ m`
-/
DefinitionDoc Multiset.toFinset as "Multiset.toFinset"

/-- `Multiset.mem_toFinset` states that
`a ∈ m.toFinset ↔ a ∈ m`.

Membership in `toFinset` is the same as membership in the multiset.

## Syntax
```
rw [Multiset.mem_toFinset]
```

## When to use it
When converting between multiset membership and finset membership.
-/
TheoremDoc Multiset.mem_toFinset as "Multiset.mem_toFinset" in "Multiset"

TheoremTab "Multiset"
NewDefinition Multiset.toFinset
NewTheorem Multiset.mem_toFinset

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
