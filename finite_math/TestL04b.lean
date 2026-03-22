import Game.Metadata

-- Option 2: Give the learner the non-membership facts
example (h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ))
    (h2 : (2 : ℕ) ∉ ({3} : Finset ℕ)) :
    ({1, 2, 3} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem h1]
  rw [Finset.card_insert_of_notMem h2]
  rw [Finset.card_singleton]

-- Option 3: Use omega instead of relying on rfl at the end
example (h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ))
    (h2 : (2 : ℕ) ∉ ({3} : Finset ℕ)) :
    ({1, 2, 3} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem h1]
  rw [Finset.card_insert_of_notMem h2]
  rw [Finset.card_singleton]
  -- does rfl or omega work here? Let's see what's left
