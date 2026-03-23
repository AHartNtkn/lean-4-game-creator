import Game.Metadata

World "CountingTechniques"
Level 5

Title "Surjection Bound in Action"

Introduction "
# Applying the Surjection Bound

Levels 2-4 introduced injection and surjection bounds as
abstract tools. Now let's apply the surjection bound to
prove something concrete.

**The problem**: Can a function `f : Fin 3 -> Fin 5` be
surjective? Intuitively, no — 3 elements can't cover all
5 targets. The surjection bound makes this rigorous:

If `f` were surjective, then by `card_le_of_surjective`
we'd have `|Fin 5| <= |Fin 3|`, i.e., `5 <= 3`. That's
absurd.

**The proof pattern**: To prove `not P`, assume `P` and
derive a contradiction. In Lean, `not P` is defined as
`P -> False`, so `intro` assumes `P` and changes the goal
to `False`.

**Your task**: Prove that no function from `Fin 3` to
`Fin 5` is surjective.
"

/-- No function from Fin 3 to Fin 5 is surjective. -/
Statement (f : Fin 3 → Fin 5) : ¬Function.Surjective f := by
  Hint "Since `not P` is `P -> False`, use `intro` to assume
  surjectivity and prove `False`."
  Hint (hidden := true) "Try `intro hsurj`."
  intro hsurj
  Hint "Now apply the surjection bound from Level 3 to get a
  cardinality inequality from the surjectivity hypothesis."
  Hint (hidden := true) "Try:
  `have h := Fintype.card_le_of_surjective f hsurj`"
  have h := Fintype.card_le_of_surjective f hsurj
  Hint "You have `h : Fintype.card (Fin 5) <= Fintype.card (Fin 3)`.
  Evaluate the cardinalities with `Fintype.card_fin` and derive a
  contradiction."
  Hint (hidden := true) "Try:
  `rw [Fintype.card_fin, Fintype.card_fin] at h`
  then `omega`."
  rw [Fintype.card_fin, Fintype.card_fin] at h
  Hint (hidden := true) "The hypothesis `h : 5 <= 3` is absurd.
  Try `omega`."
  omega

Conclusion "
The surjection bound applied contrapositively:
1. `intro hsurj` — assume surjectivity
2. `card_le_of_surjective f hsurj` — get `5 <= 3`
3. `rw [card_fin, card_fin]` — evaluate
4. `omega` — contradiction!

**The contrapositive pattern**: The surjection bound says
'surjective implies |target| <= |source|.' The contrapositive
is '|target| > |source| implies not surjective.' This is how
counting bounds are most often used in practice — not to
establish an inequality, but to *rule out* a function property.

**Dual of pigeonhole**: Pigeonhole (Level 8) says 'too many
items forces a collision' (not injective). This level says
'too few items leaves a gap' (not surjective). Both are
consequences of counting bounds:

| Property | Bound | Contrapositive |
|---|---|---|
| Injective | `|source| <= |target|` | `|source| > |target|` implies not injective |
| Surjective | `|target| <= |source|` | `|target| > |source|` implies not surjective |
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Don't let the player use injection bound for this level
DisabledTheorem Fintype.card_le_of_injective
