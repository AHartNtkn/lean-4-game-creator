import Game.Metadata

-- Fix the sdiff_subset usage
example (s t : Finset ℕ) (hs : s.card = 10) (ht : t.card = 7)
    (hi : (s ∩ t).card = 4) :
    (s ∪ t).card = 13 ∧ (s \ t).card = 6 ∧ (s \ t).card ≤ s.card := by
  constructor
  · have h := Finset.card_union_add_card_inter s t
    omega
  constructor
  · have h := Finset.card_sdiff_add_card_inter s t
    omega
  · have h := Finset.card_le_card (show s \ t ⊆ s from Finset.sdiff_subset)
    exact h

-- Actually, Part 3 is trivial and adds nothing pedagogically.
-- Let me simplify the boss to 2 parts.

-- Simpler but still meaty boss: combine 3 card lemmas
-- Part 1: card_insert
-- Part 2: inclusion-exclusion using the insert result
-- Requires: card_insert_of_notMem + card_union_add_card_inter + omega
-- This forces the learner to CHAIN results.

example (s t : Finset ℕ) (a : ℕ) (ha : a ∉ s)
    (hs : s.card = 5) (ht : t.card = 4)
    (hi : ((insert a s) ∩ t).card = 2) :
    ((insert a s) ∪ t).card = 8 := by
  -- Step 1: find |(insert a s)|
  have h1 := Finset.card_insert_of_notMem ha
  -- h1 : (insert a s).card = s.card + 1
  -- Step 2: apply inclusion-exclusion
  have h2 := Finset.card_union_add_card_inter (insert a s) t
  -- h2 : ((insert a s) ∪ t).card + ((insert a s) ∩ t).card = (insert a s).card + t.card
  omega

-- That's 3 have + omega = 4 tactic steps. Let me make it a bit richer.

-- Even better: 3-part boss
-- Given: |s| = 5, |t| = 4, |s ∩ t| = 2
-- Prove: |s ∪ t| = 7 ∧ |s \ t| = 3 ∧ (t \ s).card + (s ∩ t).card = t.card
-- The third part retrieves complement counting on t

example (s t : Finset ℕ) (hs : s.card = 5) (ht : t.card = 4)
    (hi : (s ∩ t).card = 2) :
    (s ∪ t).card = 7 ∧ (s \ t).card = 3 := by
  constructor
  · have h := Finset.card_union_add_card_inter s t
    omega
  · have h := Finset.card_sdiff_add_card_inter s t
    omega
