import Game.Metadata

World "AbstractionLadder"
Level 11

Title "Multiset Cardinality"

Introduction "
# Practicing Multiset.card

In the previous level, you learned `Multiset.count` for counting
specific elements. Now let's practice with `Multiset.card` — the
**total** element count (with multiplicity).

Recall the two key lemmas:
- `Multiset.card_cons : (a ::ₘ m).card = m.card + 1`
  — consing adds 1 to the total count
- `Multiset.coe_card : (↑l).card = l.length`
  — coercing a list to a multiset preserves the count

Together, these let you compute the cardinality of any multiset
built from lists and cons operations.

**Your task**: Given a list `l` of known length, compute the
cardinality of `a ::ₘ ↑l` (an element consed onto the multiset
version of `l`).
"

/-- Consing onto a list's multiset adds 1 to the cardinality. -/
Statement (a : ℕ) (l : List ℕ) (h : l.length = 3) :
    (a ::ₘ (↑l : Multiset ℕ)).card = 4 := by
  Hint "The outer operation is `::ₘ` (multiset cons). Use
  `Multiset.card_cons` to peel it off."
  rw [Multiset.card_cons]
  Hint "Now the goal involves `(↑l : Multiset α).card`. Use
  `Multiset.coe_card` to convert this to `l.length`."
  Hint (hidden := true) "Try `rw [Multiset.coe_card]`."
  rw [Multiset.coe_card]
  Hint "The goal is `l.length + 1 = 4`. Use the hypothesis `h`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]

Conclusion "
You used both cardinality lemmas in sequence:
1. `Multiset.card_cons` — peeled off the cons to get `.card + 1`
2. `Multiset.coe_card` — converted multiset cardinality to list length

This is the standard pattern for computing multiset cardinality:
peel off cons operations with `card_cons`, then bridge to list
length with `coe_card`.

**Connection to the ladder**: At the list level, we measure with
`.length`. At the multiset level, we measure with `.card`. The
bridge `coe_card` says these always agree: coercing a list to a
multiset doesn't change the count. The count only changes when
we climb to finsets (where duplicates are removed).
"

TheoremTab "Multiset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
