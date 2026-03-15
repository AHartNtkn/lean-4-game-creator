import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 6

Title "Subset implies card inequality"

Introduction
"
# Subset ⊆ card inequality

A fundamental fact about cardinality: if `s ⊆ t`, then `s.card ≤ t.card`.
A subset cannot have more elements than the set it is contained in.

## `Finset.card_le_card`

```
Finset.card_le_card : s ⊆ t → s.card ≤ t.card
```

This lemma takes a subset proof and produces a cardinality inequality.
It is the cardinality version of the subset relation.

## Your task

Prove that `{1, 2} ⊆ {1, 2, 3}` implies `({1, 2} : Finset Nat).card ≤ ({1, 2, 3} : Finset Nat).card`.
"

/-- A subset has at most as many elements as the containing set. -/
Statement (h : ({1, 2} : Finset Nat) ⊆ {1, 2, 3}) :
    ({1, 2} : Finset Nat).card ≤ ({1, 2, 3} : Finset Nat).card := by
  Hint "You have a subset hypothesis `h`. What lemma converts a subset
  relation into a cardinality inequality?"
  Hint (hidden := true) "Use `exact Finset.card_le_card h`."
  exact Finset.card_le_card h

Conclusion
"
You applied `Finset.card_le_card` to convert a subset relation into a
cardinality inequality.

## The proof move: V15

`Finset.card_le_card` is a key proof move (V15 in the coverage map).
It captures the principle:

> If every element of `s` is also in `t`, then `s` has at most as many
> elements as `t`.

This is used frequently in combinatorics: to bound the size of a
collection, show it is a subset of a collection whose size you know.

## How it connects to induction

The proof of `card_le_card` internally uses finset induction (on `s`):
- **Base**: `∅ ⊆ t`, and `∅.card = 0 ≤ t.card`.
- **Step**: if `s ⊆ t` and `a ∈ t` and `a ∉ s`, then
  `(insert a s).card = s.card + 1 ≤ t.card`.

You do not need to reprove it — the library version is efficient.
But understanding that induction underlies it connects this level to the
world's theme.

**In plain language**: \"A subset has fewer or equal elements. This is
the counting consequence of the inclusion relation.\"
"

/-- `Finset.card_le_card` states that `s ⊆ t → s.card ≤ t.card`.

If `s` is a subset of `t`, then `s` has at most as many elements. -/
TheoremDoc Finset.card_le_card as "Finset.card_le_card" in "Finset"

NewTheorem Finset.card_le_card
DisabledTactic trivial decide native_decide aesop simp_all
