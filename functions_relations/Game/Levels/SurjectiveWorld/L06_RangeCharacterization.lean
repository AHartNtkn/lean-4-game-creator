import Game.Metadata

World "SurjectiveWorld"
Level 6

Title "Surjective Implies Full Range"

TheoremTab "Function"

Introduction "
# Range Characterization: Forward Direction

In Image World, you learned that `Set.range f` is the set of all outputs
of `f`:

$$\\text{range}(f) = \\{y \\mid \\exists\\, x,\\; f(x) = y\\}$$

A function is surjective when EVERY element of the codomain is an output.
So if `f` is surjective, `Set.range f` should equal the entire codomain —
`Set.univ`.

**Your task**: Prove `Surjective f → Set.range f = Set.univ`.

**Proof approach**: Use `ext y` for the set equality, then prove both
directions of the membership iff using `Set.mem_range` and `Set.mem_univ`.
"

/-- Surjective f implies Set.range f = Set.univ. -/
Statement {α β : Type} {f : α → β}
    (hf : Function.Surjective f) : Set.range f = Set.univ := by
  Hint "This is a set equality, so start with `ext y` to take an
  arbitrary element and prove membership in both directions."
  Hint (hidden := true) "`ext y`."
  ext y
  Hint "The goal is `y ∈ Set.range f ↔ y ∈ Set.univ`. Split with
  `constructor`."
  constructor
  · Hint "**Forward**: `y ∈ Set.range f → y ∈ Set.univ`.
    Everything is in `Set.univ`. Use `intro _` then `exact Set.mem_univ y`."
    Hint (hidden := true) "`intro _` then `exact Set.mem_univ y`."
    intro _
    exact Set.mem_univ y
  · Hint "**Backward**: `y ∈ Set.univ → y ∈ Set.range f`.
    You need to show `y ∈ Set.range f`. Use `intro _` to discard the
    trivial hypothesis, then `rw [Set.mem_range]` to convert to
    `∃ x, f x = y`, then `exact hf y`."
    Hint (hidden := true) "`intro _` then `rw [Set.mem_range]` then `exact hf y`."
    intro _
    rw [Set.mem_range]
    exact hf y

Conclusion "
You proved the forward direction of the range characterization:

$$\\text{Surjective}(f) \\;\\;\\Longrightarrow\\;\\; \\text{range}(f) = \\text{univ}$$

**The proof shape**: Set equality via `ext y`, then both directions of
the membership iff. The forward direction is trivial (`Set.mem_univ`);
the backward direction uses surjectivity to produce a preimage.

**Key techniques used**:
- `ext y` for set equality (from Subset World)
- `Set.mem_range` to convert range membership to an existential
  (from Image World)
- `Set.mem_univ` — everything is in `Set.univ`

In the next level, you will prove the converse: if the range is the
full codomain, then the function is surjective.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Set.range_eq_univ Function.Surjective.range_eq
