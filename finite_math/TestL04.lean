import Game.Metadata

-- L04: Chain card_insert + card_singleton to compute {1,2,3}.card = 3
-- Need to check how {1,2,3} unfolds
-- {1, 2, 3} = insert 1 (insert 2 {3}) = insert 1 (insert 2 (insert 3 ∅))
-- Wait, {3} = insert 3 ∅, which is a singleton, so card_singleton works directly

-- Version with rw chain
example : ({1, 2, 3} : Finset ℕ).card = 3 := by
  -- {1, 2, 3} = insert 1 {2, 3}
  rw [show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) from by decide |> Finset.card_insert_of_notMem]
  -- now: {2, 3}.card + 1 = 3
  rw [show (2 : ℕ) ∉ ({3} : Finset ℕ) from by decide |> Finset.card_insert_of_notMem]
  -- now: {3}.card + 1 + 1 = 3
  rw [Finset.card_singleton]
  -- now: 1 + 1 + 1 = 3

-- Hmm, that's ugly. Let me try cleaner approach.
-- The learner should use have statements + omega.

-- Cleaner approach:
example : ({1, 2, 3} : Finset ℕ).card = 3 := by
  have h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ) := by decide
  have h2 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by decide
  rw [Finset.card_insert_of_notMem h1]
  rw [Finset.card_insert_of_notMem h2]
  rw [Finset.card_singleton]

-- But decide is disabled! How does the learner prove 1 ∉ {2, 3}?
-- They know how to prove non-membership from FinsetBasics L11-L12.
-- The non-membership proof from FinsetBasics uses:
--   intro h; rw [Finset.mem_insert] at h; cases h with ...
-- That's verbose. For THIS world, we're teaching cardinality, not membership.
-- So we should either:
-- 1. Allow decide for the non-membership sub-goals
-- 2. Provide the non-membership hypotheses as given
-- 3. Use a different statement

-- Option 2: Give the learner the non-membership facts
example (h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ))
    (h2 : (2 : ℕ) ∉ ({3} : Finset ℕ)) :
    ({1, 2, 3} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem h1]
  rw [Finset.card_insert_of_notMem h2]
  rw [Finset.card_singleton]

-- That works! The learner focuses on the card chain.
-- But wait - do we need omega at the end?
-- Let's see: after rw [card_singleton], the goal is 1 + 1 + 1 = 3
-- No wait, let me check...

-- After rw card_insert h1: ({2,3}).card + 1 = 3
-- After rw card_insert h2: ({3}).card + 1 + 1 = 3
-- After rw card_singleton: 1 + 1 + 1 = 3
-- Hmm, does that close by rfl or need omega?

-- Actually wait — rfl should work since 1 + 1 + 1 reduces to 3
