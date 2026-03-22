import Game.Metadata

-- Does the rfl close n + 1 + 1 = n + 2?
example (n : ℕ) : n + 1 + 1 = n + 2 := by rfl
-- Yes!

-- Concrete version with hypotheses given
example (h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ))
    (h2 : (2 : ℕ) ∉ ({3} : Finset ℕ)) :
    ({1, 2, 3} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem h1]
  rw [Finset.card_insert_of_notMem h2]
  rw [Finset.card_singleton]
  -- closes automatically
