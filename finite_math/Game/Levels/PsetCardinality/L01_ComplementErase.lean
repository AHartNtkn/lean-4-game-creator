import Game.Metadata

World "PsetCardinality"
Level 1

Title "Complement and Erase"

Introduction "
# Problem Set: Cardinality and Counting

Welcome to the cardinality problem set. You'll apply skills from
Cardinality, the Abstraction Ladder, Fintype, and Counting Types
to **fresh problems** with sparser hints.

**The collect-and-close strategy**: Most cardinality proofs in this
problem set follow a common pattern: (1) identify which card lemmas
are needed, (2) bring each into context with `have`, (3) let `omega`
combine the arithmetic. We call this **collect-and-close** — collect
the card facts, then close with `omega`. You'll use this pattern
throughout the problem set.

**Your first task**: Given two finsets `s` and `t` with known sizes
and known overlap, and an element `a` that belongs to $s \\setminus t$,
compute the cardinality of $(s \\setminus t)$ with `a` removed.

Two counting ideas work together here:
- **Complement counting** tells you $|s \\setminus t|$ from $|s|$ and $|s \\cap t|$
- **Erase counting** tells you what removing one element does to the count

Bring both facts into context with `have`, then let `omega` combine
them with the given sizes.
"

/-- Compute |(s \ t).erase a| from the sizes of s and s ∩ t. -/
Statement (s t : Finset ℕ) (a : ℕ) (ha : a ∈ s \ t)
    (hs : s.card = 12) (hi : (s ∩ t).card = 5) :
    ((s \ t).erase a).card = 6 := by
  Hint "You need two card facts. First, compute |(s \\ t)| using
  complement counting: `have h1 := Finset.card_sdiff_add_card_inter s t`"
  Hint (hidden := true) "The two `have` statements you need:
  `have h1 := Finset.card_sdiff_add_card_inter s t`
  `have h2 := Finset.card_erase_of_mem ha`
  Then `omega`."
  have h1 := Finset.card_sdiff_add_card_inter s t
  Hint "Good. `h1 : (s \\ t).card + (s ∩ t).card = s.card`.
  With `hs` and `hi`, this gives |(s \\ t)| = 7.

  Now apply `card_erase_of_mem` with `ha : a ∈ s \\ t`."
  have h2 := Finset.card_erase_of_mem ha
  Hint "`h2 : ((s \\ t).erase a).card = (s \\ t).card - 1`.
  Combined with h1, hs, and hi, `omega` can finish: 7 - 1 = 6."
  omega

Conclusion "
Two card lemmas chained on a fresh surface:

| Step | Lemma | What it gave |
|---|---|---|
| 1 | `card_sdiff_add_card_inter` | $|s \\setminus t| + 5 = 12$, so $|s \\setminus t| = 7$ |
| 2 | `card_erase_of_mem` | $|(s \\setminus t).\\text{erase}\\;a| = 7 - 1 = 6$ |

In the Cardinality world, you used these lemmas separately.
Here they work together: complement counting determines the
size of the set difference, and then erase removes one element.
The `have + omega` pattern handles both steps cleanly.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
