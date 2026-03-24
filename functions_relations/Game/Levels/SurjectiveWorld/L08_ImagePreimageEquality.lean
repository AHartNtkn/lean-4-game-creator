import Game.Metadata

World "SurjectiveWorld"
Level 8

Title "Image-Preimage Equality for Surjections"

TheoremTab "Function"

Introduction "
# Surjectivity Upgrades Inclusion to Equality

In Image World, you proved that `f '' (f ⁻¹' t) ⊆ t` for any function `f`
and set `t`. The reverse inclusion `t ⊆ f '' (f ⁻¹' t)` requires every
element of `t` to have a preimage — which is exactly what surjectivity
guarantees.

**Conclusion**: If `f` is surjective, then `f '' (f ⁻¹' t) = t` for every
set `t`. Surjectivity upgrades a conditional inclusion to an unconditional
equality.

**Proof approach**:
1. `ext y` for the set equality
2. **Forward** (`⊆`): unwinding image membership — standard pattern
3. **Backward** (`⊇`): use surjectivity to find a preimage, then show it
   lands in `f ⁻¹' t`
"

/-- If f is surjective, then f '' (f ⁻¹' t) = t. -/
Statement {α β : Type} {f : α → β} {t : Set β}
    (hf : Function.Surjective f) : f '' (f ⁻¹' t) = t := by
  Hint "This is a set equality. Start with `ext y`."
  ext y
  Hint "The goal is `y ∈ f '' (f ⁻¹' t) ↔ y ∈ t`. Split with `constructor`."
  constructor
  · Hint "**Forward**: `y ∈ f '' (f ⁻¹' t) → y ∈ t`.

    Destructure the image membership with
    `rintro ⟨x, hx, rfl⟩`

    This gives `x` with `hx : x ∈ f ⁻¹' t` (i.e., `f x ∈ t`) and
    substitutes `y = f x`."
    Hint (hidden := true) "`rintro ⟨x, hx, rfl⟩` then `exact hx`."
    rintro ⟨x, hx, rfl⟩
    Hint "After substitution, the goal is `f x ∈ t`. But
    `hx : x ∈ f ⁻¹' t` is definitionally `f x ∈ t`. Use `exact hx`."
    exact hx
  · Hint "**Backward**: `y ∈ t → y ∈ f '' (f ⁻¹' t)`.

    This is where surjectivity matters. Assume `y ∈ t` with `intro hy`,
    then use surjectivity to get a preimage:
    `obtain ⟨a, ha⟩ := hf y`"
    Hint (hidden := true) "`intro hy` then `obtain ⟨a, ha⟩ := hf y`."
    intro hy
    obtain ⟨a, ha⟩ := hf y
    Hint "Now `ha : f a = y` and `hy : y ∈ t`. You need to show
    `y ∈ f '' (f ⁻¹' t)`, i.e., there exists `x ∈ f ⁻¹' t` with `f x = y`.

    The witness is `a`. First prove `f a ∈ t` (so `a ∈ f ⁻¹' t`), then
    note `f a = y`.

    Use `have hfa : f a ∈ t := by rw [ha]; exact hy`."
    Hint (hidden := true) "`have hfa : f a ∈ t := by rw [ha]; exact hy`
    then `exact ⟨a, hfa, ha⟩`."
    have hfa : f a ∈ t := by rw [ha]; exact hy
    Hint "Now `hfa : f a ∈ t` means `a ∈ f ⁻¹' t`, and `ha : f a = y`.
    Package the witness: `exact ⟨a, hfa, ha⟩`."
    exact ⟨a, hfa, ha⟩

Conclusion "
You proved that surjective functions give **equality** in the image-preimage
round trip:

$$f \\text{ surjective} \\;\\;\\Longrightarrow\\;\\; f''(f^{-1}(t)) = t$$

Compare with the unconditional inclusion `f '' (f ⁻¹' t) ⊆ t` from Image
World — the `⊇` direction required finding a preimage for each `y ∈ t`,
which is exactly what surjectivity provides.

**Why this matters**: Without surjectivity, applying `f` then taking
preimages can lose elements (those not in the range). With surjectivity,
nothing is lost — the round trip recovers the original set exactly.

**The proof pattern**: The forward direction was pure image unwinding
(`rintro` + `exact`). The backward direction used surjectivity to produce
a preimage, verified it lands in `f ⁻¹' t` via rewriting, then packaged
the witness with angle brackets.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Set.image_preimage_eq
