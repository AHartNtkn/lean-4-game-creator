import Game.Metadata

-- Boss: Three-step straight-line proof using insert + inclusion-exclusion + omega
-- Given: a ∉ s, |s| = n, |t| = m, |(insert a s) ∩ t| = k
-- Prove: |(insert a s) ∪ t| = result

-- This requires: card_insert_of_notMem + card_union_add_card_inter + omega

example (s t : Finset ℕ) (a : ℕ) (ha : a ∉ s)
    (hs : s.card = 5) (ht : t.card = 4) (hi : ((insert a s) ∩ t).card = 2) :
    ((insert a s) ∪ t).card = 8 := by
  have h1 := Finset.card_insert_of_notMem ha
  have h2 := Finset.card_union_add_card_inter (insert a s) t
  omega

-- Good! 3 lines (2 have + omega). Tests card_insert + inclusion-exclusion + omega.

-- Make it a bit more: add a card_erase part
-- Given: a ∉ s, b ∈ s, |s| = 6, |t| = 3, |(insert a s) ∩ t| = 2
-- Part 1: |(insert a s) ∪ t| = ?
-- Part 2: |(s.erase b)| = ?
-- Both test different card lemmas.

example (s t : Finset ℕ) (a b : ℕ) (ha : a ∉ s) (hb : b ∈ s)
    (hs : s.card = 6) (ht : t.card = 3)
    (hi : ((insert a s) ∩ t).card = 1) :
    ((insert a s) ∪ t).card = 9 ∧ (s.erase b).card = 5 := by
  constructor
  · have h1 := Finset.card_insert_of_notMem ha
    have h2 := Finset.card_union_add_card_inter (insert a s) t
    omega
  · have h := Finset.card_erase_of_mem hb
    omega
