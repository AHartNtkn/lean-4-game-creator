import Game.Metadata

World "PsetCounting"
Level 4

Title "League Divisions"

Introduction "
A sports league assigns each of its `n` teams to one of 4
divisions. Each division has exactly 8 teams.

How many teams are in the league?
"

/-- If each of 4 divisions has 8 teams, the league has 32 teams. -/
Statement (n : ℕ) (f : Fin n → Fin 4)
    (hunif : ∀ d : Fin 4,
      (Finset.univ.filter (fun t : Fin n => f t = d)).card = 8) :
    n = 32 := by
  Hint (hidden := true) "The decomposition theorem requires a
  membership proof. Construct it:
  `have hmem : ∀ x ∈ (Finset.univ : Finset (Fin n)), f x ∈ (Finset.univ : Finset (Fin 4)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ x ∈ (Finset.univ : Finset (Fin n)),
    f x ∈ (Finset.univ : Finset (Fin 4)) := fun _ _ => Finset.mem_univ _
  Hint (hidden := true) "Try
  `have h := Finset.card_eq_sum_card_fiberwise hmem`."
  have h := Finset.card_eq_sum_card_fiberwise hmem
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin] at h`."
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  Hint (hidden := true) "Try
  `rw [Finset.sum_congr rfl (fun c _ => hunif c)]`."
  rw [Finset.sum_congr rfl (fun c _ => hunif c)]
  Hint (hidden := true) "Try
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`."
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

Conclusion "
Fiber decomposition expresses the total as a sum of group
sizes. When each group is uniform, the sum reduces to
multiplication: `4 * 8 = 32`.

The `fun _ _ => Finset.mem_univ _` pattern proves every
element maps into `Finset.univ`. This boilerplate always
takes the same form -- you'll need it again in the boss.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
