import Game.Metadata

-- Test: does exact? find the lattice exploit for the boss?
example (s t u : Finset ℕ) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by exact?

-- Test: does Finset.pair_comm need to be disabled for L06?
-- Already confirmed it compiles. Check if it is in the disabled list.

