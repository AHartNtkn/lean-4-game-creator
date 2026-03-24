import Game.Metadata

World "ImageWorld"
Level 4

Title "Image of the Empty Set"

TheoremTab "Set"

Introduction "
# The Image of Nothing is Nothing

Before diving into abstract structural results, let us handle the
simplest boundary case: the image of the empty set.

$$f(\\emptyset) = \\emptyset$$

Why? The image `f '' s` consists of all `y` such that there EXISTS
some `x \\in s` with `f x = y`. If `s = \\emptyset`, there are NO
elements to serve as witnesses. No witnesses means no image members.

This is the vacuous case of the existential: `\\exists x \\in \\emptyset, P(x)`
is always false, because there is no `x` in `\\emptyset` to satisfy `P`.

Compare with the other extremal case `f '' Set.univ = Set.range f`
(which you will prove in Level 12). Image sends `\\emptyset` to
`\\emptyset` and `Set.univ` to `Set.range f`.

**Proof plan**:
1. `ext y` then `constructor`
2. **Forward**: Destructure `y \\in f '' \\emptyset` -- the source
   membership `x \\in \\emptyset` is a contradiction
3. **Backward**: `y \\in \\emptyset` is itself a contradiction
"

/-- The image of the empty set is empty. -/
Statement (α β : Type) (f : α → β) : f '' (∅ : Set α) = ∅ := by
  Hint "Start with `ext y` then `constructor` as usual for set equality."
  ext y
  constructor
  -- Forward: y ∈ f '' ∅ → y ∈ ∅
  · Hint "**Forward**: If `y ∈ f '' ∅`, there exists `x ∈ ∅` with
    `f x = y`. But nothing is in `∅`!

    Use `rintro ⟨x, hx, rfl⟩` to destructure the image membership."
    Hint (hidden := true) "After `rintro ⟨x, hx, rfl⟩`, `hx : x ∈ ∅`
    which is `False`. Use `contradiction` or `exact hx.elim`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx.elim
    rintro ⟨x, hx, rfl⟩
    Hint "You have `hx : x ∈ ∅`. Since `∅` is the set with no
    elements, `x ∈ ∅` is definitionally `False`. This is a contradiction!"
    Hint (hidden := true) "`contradiction` or `exact hx.elim`."
    exact hx.elim
  -- Backward: y ∈ ∅ → y ∈ f '' ∅
  · Hint "**Backward**: If `y ∈ ∅`, that is itself a contradiction.
    Use `intro hy` to assume it."
    Hint (hidden := true) "`intro hy` then `contradiction` or `exact hy.elim`."
    intro hy
    Hint "`hy : y ∈ ∅` is `False`. This is a contradiction."
    exact hy.elim

Conclusion "
You proved `f '' ∅ = ∅` -- the image of nothing is nothing.

Both directions are trivially true because membership in `∅` is
always `False`. There are no witnesses in the empty set, so the
existential in image membership is vacuously false.

**The vacuous existential**: `∃ x ∈ ∅, P x` is always false
regardless of `P`, because there is no `x` in `∅`. This is the
foundational reason why `f '' ∅ = ∅`.

**Extremal cases**: Image sends the two extreme sets to:
- `f '' ∅ = ∅` (this level)
- `f '' Set.univ = Set.range f` (Level 12)

Compare with preimage: `f ⁻¹' ∅ = ∅` and `f ⁻¹' Set.univ = Set.univ`.
Image of everything depends on the function (its range), while
preimage of everything is always everything. Another manifestation
of the image-preimage asymmetry.

The library name is `Set.image_empty`.
"

/-- `Set.image_empty` states `f '' ∅ = ∅`. The image of the empty
set is empty -- no inputs means no outputs. -/
TheoremDoc Set.image_empty as "Set.image_empty" in "Set"

NewTheorem Set.image_empty

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_empty
