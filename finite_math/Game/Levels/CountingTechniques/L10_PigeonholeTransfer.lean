import Game.Metadata

World "CountingTechniques"
Level 10

Title "From Collision to Non-Injectivity"

Introduction "
# Using Pigeonhole Witnesses

Level 9 proved that among elements mapping to fewer targets,
two must collide. But what do you DO with the collision?

The most common use: prove the function is **not injective**.
If distinct `a` and `b` satisfy `f a = f b`, then `f` can't
be injective (injective means `f a = f b` implies `a = b`).

**The proof pattern**:
1. `obtain` the witnesses from the collision hypothesis
2. `intro` an injectivity assumption
3. Apply injectivity to the equal outputs to get `a = b`
4. This contradicts `a != b`

**Problem**: A teacher assigns 13 students to 12 project slots.
Given that two students share a slot (the collision), prove the
assignment is not injective.

**Your task**: From the collision witnesses, prove
`not Injective assignSlot`.
"

/-- A collision between distinct elements proves non-injectivity. -/
Statement (assignSlot : Fin 13 → Fin 12)
    (hcollision : ∃ a b : Fin 13, a ≠ b ∧ assignSlot a = assignSlot b) :
    ¬Function.Injective assignSlot := by
  Hint "First, extract the witnesses from the existential.
  Use `obtain` to destructure `hcollision` into the two
  students `a`, `b`, their distinctness `hne`, and the
  collision `heq`."
  Hint (hidden := true) "Try:
  `obtain ⟨a, b, hne, heq⟩ := hcollision`"
  obtain ⟨a, b, hne, heq⟩ := hcollision
  Hint "Now assume `assignSlot` is injective and derive a
  contradiction. Since `not P` is `P -> False`, use `intro`."
  Hint (hidden := true) "Try `intro hinj`."
  intro hinj
  Hint "Apply the injectivity hypothesis `hinj` to `heq`:
  since `assignSlot a = assignSlot b` and `assignSlot` is
  injective, we get `a = b`. But `hne` says `a != b`."
  Hint (hidden := true) "Try `exact hne (hinj heq)`."
  exact hne (hinj heq)

Conclusion "
From collision to non-injectivity:
1. `obtain ⟨a, b, hne, heq⟩ := hcollision` — extract witnesses
2. `intro hinj` — assume injectivity
3. `exact hne (hinj heq)` — `hinj heq : a = b` contradicts `hne`

**The full pigeonhole workflow**:
- **Level 9**: *Find* collisions — `exists_ne_map_eq_of_card_lt`
  gives you `exists a b, a != b and f a = f b`
- **Level 10**: *Use* collisions — extract witnesses with `obtain`,
  then chain `hinj heq` to contradict `hne`

In practice, `not_injective_of_card_lt` (Level 8) packages both
steps into one theorem. But understanding the two-step process
is valuable: sometimes you need the actual witnesses (the
colliding pair), not just the negative statement.

**Classic pigeonhole applications**:
- Among $n + 1$ integers, two have the same remainder mod $n$
  (Level 9 finds the pair; this level proves the map is non-injective)
- In any group of 367 people, two share a birthday
- Among 5 points in a unit square, two are within distance
  $\\sqrt{2}/2$ (divide into 4 quadrants)

The key skill is **recognition**: seeing that a problem involves
mapping more objects to fewer categories.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.exists_ne_map_eq_of_card_lt_of_maps_to Fintype.not_injective_of_card_lt
