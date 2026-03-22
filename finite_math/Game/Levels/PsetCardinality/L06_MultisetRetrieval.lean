import Game.Metadata

World "PsetCardinality"
Level 6

Title "Multiset Cardinality"

Introduction "
# Multiset Retrieval

In the Abstraction Ladder, you learned how multisets track
cardinality: consing adds 1, and coercing from a list preserves
the count.

**Your task**: Given a list `l` of known length, compute the
cardinality of the multiset `a ::_m b ::_m uparrow l` — two elements
consed onto the multiset version of `l`.

Peel off each cons, bridge to list length, then finish.
"

/-- Compute the cardinality of a multiset built from a list with two cons operations. -/
Statement (l : List ℕ) (a b : ℕ) (hlen : l.length = 4) :
    (a ::ₘ b ::ₘ (↑l : Multiset ℕ)).card = 6 := by
  Hint "The outer operation is multiset cons. What lemma peels
  off a cons from `Multiset.card`?"
  Hint (hidden := true) "Peel off both cons operations, then bridge to list length:
  `rw [Multiset.card_cons, Multiset.card_cons, Multiset.coe_card, hlen]`"
  rw [Multiset.card_cons]
  Hint (hidden := true) "One cons peeled off. Continue: `rw [Multiset.card_cons]`."
  rw [Multiset.card_cons]
  Hint "The goal now involves `(uparrow l : Multiset N).card`. How do you
  convert multiset cardinality to list length?"
  Hint (hidden := true) "Try `rw [Multiset.coe_card]`."
  rw [Multiset.coe_card]
  Hint (hidden := true) "Substitute `hlen` to finish."
  rw [hlen]

Conclusion "
Three Multiset lemmas from the Abstraction Ladder, applied in a
counting context:

| Step | Lemma | Effect |
|---|---|---|
| 1-2 | `Multiset.card_cons` | peeled off each consed element |
| 3 | `Multiset.coe_card` | converted multiset card to list length |

**Pattern**: To compute the cardinality of a multiset built from
a list, peel off cons operations with `card_cons`, then bridge
to list length with `coe_card`. This is the same rewrite-and-reduce
pattern you use for Fintype decompositions — just at a different
layer of the abstraction ladder.
"

TheoremTab "Multiset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
