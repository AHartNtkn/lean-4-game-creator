import Game.Metadata

World "Powerset"
Level 1

Title "The Empty Set Is Always a Subset"

Introduction "
# Meet the Powerset

Given a finset `s`, the **powerset** `s.powerset` is the finset of all
subsets of `s`. If `s = {1, 2, 3}`, then `s.powerset` contains every
possible sub-collection: `∅`, `{1}`, `{2}`, `{3}`, `{1,2}`, `{1,3}`,
`{2,3}`, and `{1,2,3}` — that's $2^3 = 8$ subsets in total.

The key characterization lemma is:

$$t \\in s.\\text{powerset} \\iff t \\subseteq s$$

In Lean: `Finset.mem_powerset : t ∈ s.powerset ↔ t ⊆ s`.

This turns powerset membership into a subset question, which you
already know how to handle.

**Your task**: Prove that the empty set is in the powerset of any
finset `s`. Strategy: rewrite the powerset membership into a subset
claim, then use the fact that the empty set is a subset of everything.
"

/-- `Finset.powerset s` is the finset of all subsets of `s`.

## Type
`Finset.powerset : Finset α → Finset (Finset α)`

## Key characterization
`Finset.mem_powerset : t ∈ s.powerset ↔ t ⊆ s`

A finset `t` is in the powerset of `s` exactly when `t` is a
subset of `s`.

## Cardinality
`Finset.card_powerset : (s.powerset).card = 2 ^ s.card`

A finset with `n` elements has `2^n` subsets.

## Example
If `s = {1, 2}`, then `s.powerset = {∅, {1}, {2}, {1, 2}}`.
-/
DefinitionDoc Finset.powerset as "Finset.powerset"

/-- `Finset.mem_powerset` states that `t ∈ s.powerset ↔ t ⊆ s`.

## Syntax
```
rw [Finset.mem_powerset]     -- in the goal
rw [Finset.mem_powerset] at h -- in a hypothesis
```

## When to use it
When you see `t ∈ s.powerset` and want to convert it to `t ⊆ s`
(or vice versa). This is the fundamental bridge between powerset
membership and subset reasoning.

## Example
If the goal is `t ∈ s.powerset`, then `rw [Finset.mem_powerset]`
changes it to `t ⊆ s`.

## Common misuse
Remember that `⊆` for finsets means `∀ x ∈ t, x ∈ s`, so after
rewriting you may need `intro x hx` to proceed.
-/
TheoremDoc Finset.mem_powerset as "Finset.mem_powerset" in "Finset"

/-- `Finset.empty_subset s` states that `∅ ⊆ s` for any finset `s`.

## Syntax
```
exact Finset.empty_subset s
```

## When to use it
When the goal is `∅ ⊆ s` — the empty set is a subset of everything.
-/
TheoremDoc Finset.empty_subset as "Finset.empty_subset" in "Finset"

/-- The empty set is in the powerset of any finset. -/
Statement (s : Finset ℕ) : ∅ ∈ s.powerset := by
  Hint "The goal is `∅ ∈ s.powerset`. This asks: is the empty set a
  subset of `s`? Use `Finset.mem_powerset` to convert the powerset
  membership into a subset statement."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset]`."
  rw [Finset.mem_powerset]
  Hint "Now the goal is `∅ ⊆ s` — the empty set is a subset of
  everything. The lemma `Finset.empty_subset` says exactly this."
  Hint (hidden := true) "Try `exact Finset.empty_subset s`."
  exact Finset.empty_subset s

Conclusion "
You proved `∅ ∈ s.powerset` by:
1. Rewriting with `mem_powerset` to get `∅ ⊆ s`
2. Applying `empty_subset`

**Reusable recipe**: To prove `t ∈ s.powerset`, rewrite with
`mem_powerset` to convert to `t ⊆ s`, then prove the subset claim.
This is the fundamental pattern for all powerset reasoning.

In ordinary math: the empty set is a subset of every set, so it
appears in every powerset.
"

NewDefinition Finset.powerset
NewTheorem Finset.mem_powerset Finset.empty_subset

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self
