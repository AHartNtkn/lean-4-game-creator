import Game.Metadata

World "PsetCounting"
Level 5

Title "Category Sizes"

Introduction "
A function `f : Fin 10 → Fin 3` assigns each of 10 items to
one of 3 categories.

Prove that some category contains more than 3 items.
"

/-- With 10 items in 3 categories, some category has more than 3. -/
Statement (f : Fin 10 → Fin 3) :
    ∃ c : Fin 3,
      3 < (Finset.univ.filter (fun t : Fin 10 => f t = c)).card := by
  Hint "The goal asks you to show something EXISTS. What if
  nothing satisfies it? Assume the opposite and look for a
  contradiction with the total count."
  by_contra hall
  Hint (hidden := true) "Try `push_neg at hall`."
  push_neg at hall
  -- hall : ∀ c, (univ.filter ...).card ≤ 3
  Hint (hidden := true) "Decompose the total count into
  category sizes. Start with the membership boilerplate:
  `have hmem : ∀ x ∈ (Finset.univ : Finset (Fin 10)), f x ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ x ∈ (Finset.univ : Finset (Fin 10)),
    f x ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _
  Hint (hidden := true) "Try
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`
  then `rw [Finset.card_univ, Fintype.card_fin] at hfib`."
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  Hint (hidden := true) "Bound the sum using `hall`:
  `have hbound := Finset.sum_le_sum (fun (c : Fin 3) (_ : c ∈ Finset.univ) => hall c)`
  then `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound`
  then `omega`."
  have hbound := Finset.sum_le_sum
    (fun (c : Fin 3) (_ : c ∈ Finset.univ) => hall c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hbound
  omega

Conclusion "
The proof uses contradiction and double counting: assuming
every category has at most 3 items, the total is at most
`3 * 3 = 9`, contradicting the 10 items.

This is the **counting contradiction pattern** from
CountingTechniques L16: `by_contra` + `push_neg` converts
a negated existential into a universal bound, then fiber
decomposition + sum bounding produces a numerical
contradiction. Recognizing this pattern is the key --
the level looks like pigeonhole, but the goal asks about
fiber *sizes*, not just collisions.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
