import Game.Metadata

World "SurjectiveWorld"
Level 7

Title "Range Characterization: Backward Direction"

TheoremTab "Function"

Introduction "
# Full Range Implies Surjective

In the previous level, you proved that a surjective function has full range.
Now prove the converse: if `Set.range f = Set.univ`, then `f` is surjective.

**The idea**: If the range is everything, then every `b` is in the range.
Being in the range means `∃ x, f x = b` — exactly surjectivity.

**Proof approach**:
1. `intro b` to take an arbitrary codomain element
2. Show `b ∈ Set.range f` (since `Set.range f = Set.univ` and everything
   is in `Set.univ`)
3. Convert range membership to an existential with `Set.mem_range`

**Tip**: To show `b ∈ Set.range f`, you can rewrite `Set.range f` to
`Set.univ` using the hypothesis, then use `Set.mem_univ`.
"

/-- If the range of f is the full codomain, then f is surjective. -/
Statement {α β : Type} {f : α → β}
    (h : Set.range f = Set.univ) : Function.Surjective f := by
  Hint "Start with `intro b` as always for a surjectivity proof."
  intro b
  Hint "You need `∃ a, f a = b`. The idea: since `Set.range f = Set.univ`,
  every element is in `Set.range f`.

  Start by noting that everything is in `Set.univ`:
  `have hb : b ∈ Set.univ := Set.mem_univ b`"
  Hint (hidden := true) "`have hb : b ∈ Set.univ := Set.mem_univ b`."
  Branch
    have hb : b ∈ Set.range f := by rw [h]; exact Set.mem_univ b
    Hint "Now `hb : b ∈ Set.range f`. Convert to the existential form:
    `rw [Set.mem_range] at hb`"
    rw [Set.mem_range] at hb
    Hint "Now `hb : ∃ x, f x = b` — exactly the goal. Use `exact hb`."
    exact hb
  have hb : b ∈ Set.univ := Set.mem_univ b
  Hint "Now `hb : b ∈ Set.univ`. Since `h : Set.range f = Set.univ`,
  rewriting backward replaces `Set.univ` with `Set.range f`:

  `rw [← h] at hb`"
  Hint (hidden := true) "`rw [← h] at hb`."
  rw [← h] at hb
  Hint "Now `hb : b ∈ Set.range f`. Convert to the existential form:
  `rw [Set.mem_range] at hb`"
  rw [Set.mem_range] at hb
  Hint "Now `hb : ∃ x, f x = b` — exactly the goal. Use `exact hb`."
  exact hb

Conclusion "
You proved the backward direction:

$$\\text{range}(f) = \\text{univ} \\;\\;\\Longrightarrow\\;\\; \\text{Surjective}(f)$$

Together with Level 6, you have proved the full characterization:

$$\\text{Surjective}(f) \\;\\;\\Longleftrightarrow\\;\\; \\text{range}(f) = \\text{univ}$$

**Forward direction** (Level 6): If every `b` has a preimage, then the range
contains everything, so it equals `Set.univ`.

**Backward direction** (this level): If `Set.range f = Set.univ`, then
`b ∈ Set.range f` for every `b`, which means `∃ x, f x = b` — exactly
surjectivity.

**Cross-world connection**: In Image World, you learned about `Set.range`
and proved properties like `f '' Set.univ = Set.range f` and
`f '' (f ⁻¹' t) ⊆ t` with equality when `t ⊆ Set.range f`. Now you know:
surjectivity is exactly the condition `Set.range f = Set.univ`, which makes
`t ⊆ Set.range f` hold for ALL `t`. In the next level, you will use this
to prove `f '' (f ⁻¹' t) = t` when `f` is surjective — upgrading the
conditional inclusion to an unconditional equality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Set.range_eq_univ Function.Surjective.range_eq
