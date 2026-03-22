import Game.Metadata

-- 3-part boss: inclusion-exclusion + complement counting + card_erase chain
-- Given: |s| = 8, |t| = 5, |s ∩ t| = 3, a ∈ s, a ∉ t
-- Part 1: |s ∪ t| = 10
-- Part 2: |s \ t| = 5
-- Part 3: |(s.erase a) \ t| = 4
-- Part 3 requires: card_erase + card_sdiff reasoning, OR
-- use fact that (s.erase a) \ t = (s \ t).erase a (since a ∉ t → a ∈ s \ t)
-- That might be too complex. Let me try.

-- Actually, let me test whether (s.erase a) \ t = (s \ t).erase a
-- or rather, whether card_sdiff_add_card_inter works on s.erase a
example (s t : Finset ℕ) (a : ℕ) (ha : a ∈ s) (hat : a ∉ t)
    (hs : s.card = 8) (ht : t.card = 5) (hi : (s ∩ t).card = 3) :
    (s ∪ t).card = 10 ∧ (s \ t).card = 5 ∧ ((s.erase a) \ t).card = 4 := by
  constructor
  · have h := Finset.card_union_add_card_inter s t
    omega
  constructor
  · have h := Finset.card_sdiff_add_card_inter s t
    omega
  · -- Need to show |(s.erase a) \ t| = 4
    -- Key insight: a ∈ s \ t (since a ∈ s and a ∉ t)
    -- So (s.erase a) \ t = (s \ t).erase a  (erase distributes over sdiff... does it?)
    -- Actually, (s.erase a) \ t = (s \ t).erase a because:
    -- x ∈ (s.erase a) \ t ↔ x ∈ s ∧ x ≠ a ∧ x ∉ t ↔ x ∈ s \ t ∧ x ≠ a ↔ x ∈ (s \ t).erase a
    -- So |(s.erase a) \ t| = |(s \ t).erase a| = |s \ t| - 1 = 5 - 1 = 4
    -- But proving (s.erase a) \ t = (s \ t).erase a might be complex for the learner.
    -- Alternative: use card_sdiff_add_card_inter on (s.erase a) and t
    have h1 := Finset.card_sdiff_add_card_inter (s.erase a) t
    -- h1 : ((s.erase a) \ t).card + ((s.erase a) ∩ t).card = (s.erase a).card
    have h2 := Finset.card_erase_of_mem ha
    -- h2 : (s.erase a).card = s.card - 1
    -- Need: (s.erase a) ∩ t = s ∩ t (since a ∉ t, erasing a doesn't remove anything from the intersection)
    -- This is a non-trivial ext proof...
    -- The learner hasn't been taught this relationship.
    -- This is getting too complex for a boss.
    sorry

-- OK, the 3rd part is too complex. Let me go with the clean 2-part boss.
-- But add more substance: make the numbers require ALL three arithmetic hypotheses.

-- Alternative approach: make the boss a straight-line proof (no constructor)
-- that uses 4+ different card lemmas

-- Boss: Given a subset chain and an insert, compute a final cardinality
-- Given: t ⊆ s, |s| = 6, |t| = 2, a ∉ s
-- Prove: |(insert a s) \ t| = 5
-- Requires: card_insert_of_notMem + card_sdiff_of_subset + omega
-- And the learner needs to establish t ⊆ insert a s

example (s t : Finset ℕ) (a : ℕ) (ha : a ∉ s) (hsub : t ⊆ s)
    (hs : s.card = 6) (ht : t.card = 2) :
    ((insert a s) \ t).card = 5 := by
  -- t ⊆ insert a s (since t ⊆ s ⊆ insert a s)
  have hsub' : t ⊆ insert a s := Finset.Subset.trans hsub (Finset.subset_insert a s)
  -- |(insert a s) \ t| = |insert a s| - |t|
  have h1 := Finset.card_sdiff_of_subset hsub'
  -- |insert a s| = |s| + 1
  have h2 := Finset.card_insert_of_notMem ha
  omega

-- That's 4 lines: have, have, have, omega. Better!
-- But card_sdiff_of_subset hasn't been introduced (only card_sdiff_add_card_inter).
-- Let me check if card_sdiff_of_subset is needed or if I can use card_sdiff_add_card_inter
-- and the fact that since t ⊆ s, s ∩ t = t (so |s ∩ t| = |t|).

-- Using only taught lemmas:
example (s t : Finset ℕ) (a : ℕ) (ha : a ∉ s) (hsub : t ⊆ s)
    (hs : s.card = 6) (ht : t.card = 2) :
    ((insert a s) \ t).card = 5 := by
  -- Step 1: |insert a s| = |s| + 1 = 7
  have h1 := Finset.card_insert_of_notMem ha
  -- Step 2: complement counting on insert a s and t
  have h2 := Finset.card_sdiff_add_card_inter (insert a s) t
  -- h2: |(insert a s) \ t| + |(insert a s) ∩ t| = |insert a s|
  -- Need: |(insert a s) ∩ t| = |t| (since t ⊆ s ⊆ insert a s → t ⊆ insert a s → (insert a s) ∩ t = t)
  -- This requires Finset.inter_eq_right or similar
  -- Hmm, this is getting complicated for the learner.
  sorry

-- The fundamental issue: complement counting gives |(insert a s) \ t| + |(insert a s) ∩ t| = |insert a s|
-- but deriving |(insert a s) ∩ t| from the hypotheses requires ext or subset reasoning.
-- That's not card-level reasoning anymore.

-- Let me just go with the clean 2-part boss using hypotheses that directly match.
