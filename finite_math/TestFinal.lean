import Game.Metadata

-- Verify Finset.pair_comm compiles and closes L06
example : ({1, 2} : Finset ℕ) = {2, 1} := Finset.pair_comm 1 2

-- Verify @inf_sup_right with explicit type closes boss
example (s t u : Finset ℕ) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
  @inf_sup_right (Finset ℕ) _ s t u

-- Verify Finset.Subset.antisymm exists (for L06 alternative approach check)
example (s t : Finset ℕ) (h1 : s ⊆ t) (h2 : t ⊆ s) : s = t :=
  Finset.Subset.antisymm h1 h2

