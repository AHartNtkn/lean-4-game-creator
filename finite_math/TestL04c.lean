import Game.Metadata

-- More pedagogically focused: chain two inserts on abstract set
example (s : Finset ℕ) (a b : ℕ) (ha : a ∉ s) (hb : b ∉ insert a s) :
    (insert b (insert a s)).card = s.card + 2 := by
  rw [Finset.card_insert_of_notMem hb]
  rw [Finset.card_insert_of_notMem ha]

-- OK but does omega close s.card + 1 + 1 = s.card + 2?
-- Let me check if it's needed
-- After rw card_insert hb: (insert a s).card + 1 = s.card + 2
-- After rw card_insert ha: s.card + 1 + 1 = s.card + 2
-- Is that definitionally equal? Probably not — needs omega or ring
example (n : ℕ) : n + 1 + 1 = n + 2 := by omega

-- So the proof needs omega at the end
example (s : Finset ℕ) (a b : ℕ) (ha : a ∉ s) (hb : b ∉ insert a s) :
    (insert b (insert a s)).card = s.card + 2 := by
  rw [Finset.card_insert_of_notMem hb]
  rw [Finset.card_insert_of_notMem ha]
  omega
