import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 11

Title "The cardinality inequality"

Introduction
"
# From specific instance to general principle

In Level 10, you saw that `[1, 2, 1, 3]` has multiset cardinality 4 but
finset cardinality 3. The specific numbers (4 and 3) are not the point --
what matters is the **inequality**: the finset can never have **more**
elements than the multiset.

## `Multiset.toFinset_card_le`

This general fact is a theorem in mathlib:

```
Multiset.toFinset_card_le : m.toFinset.card ≤ m.card
```

The finset obtained by deduplication has at most as many elements as the
original multiset. Equality holds exactly when the multiset already has
no duplicates.

## Your task

Prove this inequality for the specific multiset `↑[1, 2, 1, 3]`.

Instead of computing both sides and comparing (which `decide` could do),
use the general lemma `exact Multiset.toFinset_card_le _`. The
underscore `_` tells Lean to fill in the multiset argument automatically.

This demonstrates the **derive-then-instantiate** pattern: a general
theorem (`toFinset_card_le`) gives you the specific instance for free.
"

/-- The finset cardinality is at most the multiset cardinality. -/
Statement : (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset.card ≤
    Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) := by
  Hint "The goal is an inequality: finset cardinality ≤ multiset cardinality.
  Rather than computing both sides, apply the general theorem directly.
  What lemma states that `m.toFinset.card ≤ m.card` for any multiset `m`?"
  Hint (hidden := true) "Use `exact Multiset.toFinset_card_le _`. The `_` lets Lean
  infer the multiset argument."
  exact Multiset.toFinset_card_le _

Conclusion
"
You applied a general theorem to a specific instance. The proof
`exact Multiset.toFinset_card_le _` works for **any** multiset, not just
`↑[1, 2, 1, 3]`.

This is a different proof move from what you have been doing. Instead of
computing (`decide`) or reducing (`rw` + `rfl`), you cited a known result
(`exact theorem`). In mathematical writing, this is the difference between
\"verify by calculation\" and \"this follows from Theorem X.\"

**When does equality hold?** The inequality `m.toFinset.card ≤ m.card` is
strict when `m` has duplicates (like `↑[1, 2, 1, 3]`, where 4 > 3). It is
an equality when `m` has no duplicates -- i.e., when `m.Nodup` holds.

You saw `List.Nodup` in the Lists world (W3). The property `Multiset.Nodup`
is the multiset analogue, and in fact `Multiset.Nodup (↑l) ↔ l.Nodup` --
they are the same condition, just lifted to the quotient. You will see this
connection in the next level.

**In plain language**: \"A set can never have more elements than the bag it
came from, because deduplication can only remove things, not add them.\"
"

/-- `Multiset.toFinset_card_le` states that `m.toFinset.card ≤ m.card`.
The finset obtained by removing duplicates has at most as many elements as
the original multiset. Equality holds exactly when the multiset has no
duplicates (`m.Nodup`). -/
TheoremDoc Multiset.toFinset_card_le as "Multiset.toFinset_card_le" in "Multiset"

NewTheorem Multiset.toFinset_card_le
DisabledTactic trivial decide native_decide simp aesop simp_all omega
