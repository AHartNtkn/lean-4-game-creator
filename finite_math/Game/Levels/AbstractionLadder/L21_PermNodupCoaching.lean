import Game.Metadata

World "AbstractionLadder"
Level 21

Title "Permutations Preserve Nodup"

Introduction "
# Perm.nodup_iff: Transferring Nodup Across Permutations

If two lists are permutations of each other and one has no duplicates,
then the other has no duplicates too. This makes sense: rearranging
elements can't create or destroy duplicates.

The formal statement:

`List.Perm.nodup_iff : l₁.Perm l₂ → (l₁.Nodup ↔ l₂.Nodup)`

Given a permutation `hp : l₁.Perm l₂`, you get an iff:
- `hp.nodup_iff.mp hnd` converts `hnd : l₁.Nodup` to `l₂.Nodup`
- `hp.nodup_iff.mpr hnd` converts `hnd : l₂.Nodup` to `l₁.Nodup`

**New pattern: `.mp` and `.mpr`** — If you have `h : P ↔ Q` (an iff),
then `h.mp` extracts the forward direction `P → Q`, and `h.mpr`
extracts the backward direction `Q → P`. You use `rw` to apply iffs
as rewrites, but `.mp`/`.mpr` to apply them as functions.

**Your task**: Given `hp : l₁.Perm l₂` and `hnd : l₁.Nodup`, prove
`l₂.Nodup`.
"

/-- Permutations preserve the no-duplicates property. -/
Statement (l₁ l₂ : List ℕ) (hp : l₁.Perm l₂) (hnd : l₁.Nodup) :
    l₂.Nodup := by
  Hint "Use `hp.nodup_iff` to get the iff between `l₁.Nodup` and
  `l₂.Nodup`, then apply the forward direction `.mp` to `hnd`."
  Hint (hidden := true) "Try `exact hp.nodup_iff.mp hnd`."
  exact hp.nodup_iff.mp hnd

Conclusion "
`Perm.nodup_iff` is the key tool for transferring nodup proofs across
permutations. The pattern `hp.nodup_iff.mp hnd` says: 'since `l₁` and
`l₂` have the same elements (just rearranged), and `l₁` has no
duplicates, then `l₂` has no duplicates either.'

**Why this matters for the boss**: The boss asks you to prove
something about `l₂.toFinset.card` given that `l₁` has no duplicates.
You'll need `Perm.nodup_iff` to establish that `l₂` has no duplicates
too — which is required by `toFinset_card_of_nodup`.

**The .mp / .mpr pattern**: Given `h : P ↔ Q`:
- `h.mp` goes forward: `P → Q`
- `h.mpr` goes backward: `Q → P`
"

/-- `List.Perm.nodup_iff` states that
`l₁.Perm l₂ → (l₁.Nodup ↔ l₂.Nodup)`.

Permutations preserve the nodup property.

## Syntax
```
have hnd2 := hp.nodup_iff.mp hnd
-- where hp : l₁.Perm l₂, hnd : l₁.Nodup
```

## When to use it
When you have a permutation and need to transfer a nodup proof
from one list to the other.
-/
TheoremDoc List.Perm.nodup_iff as "List.Perm.nodup_iff" in "List"

TheoremTab "List"
NewTheorem List.Perm.nodup_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith rwa
DisabledTheorem List.perm_cons_erase List.Perm.decidable
