import Game.Metadata

World "SubgroupBasics"
Level 7

Title "Destructuring with `obtain`"

Introduction
"
When you have a conjunction hypothesis `h : P ∧ Q`, projections like
`h.1` and `h.2` work but can be hard to read. The `obtain` tactic
gives you named components instead:

`obtain ⟨hp, hq⟩ := h`

This replaces `h` with two hypotheses: `hp : P` and `hq : Q`.

In this level, you have `a ∈ H ⊓ K` and need to prove `a ∈ K ∧ a ∈ H`
— the conjunction with the two parts **swapped**. The math is
trivial; the point is to practice `obtain`.
"

/-- The `obtain` tactic destructures a hypothesis into its components.

If `h : P ∧ Q`, then `obtain ⟨hp, hq⟩ := h` gives you `hp : P` and
`hq : Q`.

If `h : ∃ x, P x`, then `obtain ⟨x, hx⟩ := h` gives you `x` and
`hx : P x`.

The angle brackets `⟨⟩` are typed `\\<` and `\\>`.

You can also nest patterns: `obtain ⟨⟨h1, h2⟩, h3⟩ := h` works for
`h : (P ∧ Q) ∧ R`.

Use `obtain` whenever you need to take apart a conjunction or
existential hypothesis. -/
TacticDoc obtain

NewTactic obtain

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G)
    (a : G) (ha : a ∈ H ⊓ K) : a ∈ K ∧ a ∈ H := by
  Hint "First, convert `ha` from intersection membership to a
  conjunction: `rw [Subgroup.mem_inf] at ha`. Then destructure
  it with `obtain ⟨hH, hK⟩ := ha` to get the two parts."
  rw [Subgroup.mem_inf] at ha
  Hint "Now `ha : a ∈ H ∧ a ∈ K`. Use `obtain ⟨hH, hK⟩ := ha`
  to split it into `hH : a ∈ H` and `hK : a ∈ K`."
  Branch
    -- Learner uses .1/.2 directly without obtain
    Hint (hidden := true) "You can use `exact ⟨ha.2, ha.1⟩` with
    `.1`/`.2` projections. This works, but `obtain` gives meaningful
    names — essential when proofs get longer. Try it the `obtain` way."
    exact ⟨ha.2, ha.1⟩
  obtain ⟨hH, hK⟩ := ha
  Hint "You have `hH : a ∈ H` and `hK : a ∈ K`. The goal asks for
  `a ∈ K ∧ a ∈ H` — the swapped order. Build the conjunction with
  `exact ⟨hK, hH⟩`."
  exact ⟨hK, hH⟩

Conclusion
"
`obtain ⟨h1, h2⟩ := h` is the standard way to split a conjunction
hypothesis. It's cleaner than `h.1` and `h.2` because you get
meaningful names — which matters as proofs grow.

You'll use `obtain` constantly from now on: any time you have a
conjunction, existential, or other structure you need to take apart.
"
