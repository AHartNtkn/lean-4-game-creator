import Game.Metadata

World "ImageWorld"
Level 10

Title "Image Under Composition"

TheoremTab "Set"

Introduction "
# Image Distributes Over Composition

In Preimage World, you proved that preimage respects composition:
`(g ∘ f) ⁻¹' u = f ⁻¹' (g ⁻¹' u)`. Now you will prove the dual
result for images:

$$(g \\circ f)(s) = g(f(s))$$

Applying the composed function directly gives the same result as
applying `f` first, then applying `g` to the output.

**The proof exercises nested destructuring**: The backward direction
requires destructuring TWO levels of image membership. If
`y ∈ g '' (f '' s)`, there exists `z ∈ f '' s` with `g z = y`, and
within that, there exists `x ∈ s` with `f x = z`. The pattern
`rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩` handles both levels at once.

**Proof plan**:
1. `ext y` then `constructor`
2. **Forward**: Destructure `(g ∘ f) '' s` membership, then construct
   nested image membership in `g '' (f '' s)`
3. **Backward**: Nested destructuring, then construct `(g ∘ f) '' s`
   membership directly
"

/-- Image distributes over function composition. -/
Statement (α β γ : Type) (f : α → β) (g : β → γ) (s : Set α) :
    (g ∘ f) '' s = g '' (f '' s) := by
  Hint "Start with `ext y` then `constructor`."
  ext y
  constructor
  -- Forward: y ∈ (g ∘ f) '' s → y ∈ g '' (f '' s)
  · Hint "**Forward**: Destructure `y ∈ (g ∘ f) '' s` with
    `rintro ⟨x, hx, rfl⟩`. This gives `x ∈ s` and `y = (g ∘ f) x = g (f x)`."
    Hint (hidden := true) "After destructuring, the goal is
    `g (f x) ∈ g '' (f '' s)`. Build the nested image:
    `exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩`.

    The inner part `⟨x, hx, rfl⟩` proves `f x ∈ f '' s`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
    rintro ⟨x, hx, rfl⟩
    Hint "The goal is `g (f x) ∈ g '' (f '' s)`. You need to provide
    a witness in `f '' s` that maps to `g (f x)` under `g`.

    The witness is `f x`. Use `use f x` to provide it."
    Hint (hidden := true) "`use f x` then `constructor`,
    `exact ⟨x, hx, rfl⟩`, `rfl`.

    Or in one step: `exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩`."
    Branch
      exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
    use f x
    Hint "The goal splits into `f x ∈ f '' s` and `g (f x) = g (f x)`.
    Use `constructor` to split."
    constructor
    · Hint "Prove `f x ∈ f '' s`. The witness is `x` with `hx : x ∈ s`."
      Hint (hidden := true) "`exact ⟨x, hx, rfl⟩`"
      exact ⟨x, hx, rfl⟩
    · Hint "Prove `g (f x) = g (f x)`."
      rfl
  -- Backward: y ∈ g '' (f '' s) → y ∈ (g ∘ f) '' s
  · Hint "**Backward**: `y ∈ g '' (f '' s)` has TWO levels of
    existential: there exists `z ∈ f '' s` with `g z = y`, and
    there exists `x ∈ s` with `f x = z`.

    Use nested destructuring:
    `rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩`

    This gives `x ∈ s` and substitutes both `z = f x` and `y = g (f x)`."
    Hint (hidden := true) "After nested destructuring, the goal is
    `(g ∘ f) x ∈ (g ∘ f) '' s`. The witness is `x`:
    `exact ⟨x, hx, rfl⟩`."
    Branch
      intro hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, hx, rfl⟩
    rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    Hint "After nested destructuring, `x ∈ s` and the goal is
    `g (f x) ∈ (g ∘ f) '' s`. Since `(g ∘ f) x = g (f x)`, the
    witness is just `x`."
    Hint (hidden := true) "`exact ⟨x, hx, rfl⟩`"
    exact ⟨x, hx, rfl⟩

Conclusion "
You proved `(g ∘ f) '' s = g '' (f '' s)` -- image distributes
over composition!

**The nested destructuring pattern**: The backward direction used
`rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩` to peel off two layers of image
membership at once. This is a natural extension of the single-layer
`rintro ⟨x, hx, rfl⟩` pattern you have been using.

**Forward direction -- building nested images**: The forward direction
required `⟨f x, ⟨x, hx, rfl⟩, rfl⟩` -- an image membership proof
INSIDE another image membership proof. The outer witness is `f x ∈ f '' s`,
proved by the inner anonymous constructor `⟨x, hx, rfl⟩`.

**Dual to preimage composition**: Compare with `(g ∘ f) ⁻¹' u = f ⁻¹' (g ⁻¹' u)`
from Preimage World. Both say composition distributes, but preimage
reverses the order (`f` then `g` on the right) while image preserves
it (`f` then `g` on both sides).

**Vocabulary**: This order-preservation vs order-reversal has standard
names. Image is **covariant**: it preserves the composition order
(`(g ∘ f) '' s = g '' (f '' s)` -- `f` first, then `g`, on both sides).
Preimage is **contravariant**: it reverses the order
(`(g ∘ f) ⁻¹' u = f ⁻¹' (g ⁻¹' u)` -- `g` first on the left, `f` first
on the right). These terms will reappear in later courses whenever
operations interact with composition.

The library name is `Set.image_comp`.
"

/-- `Set.image_comp` states `(g ∘ f) '' s = g '' (f '' s)`. Image
distributes over function composition. -/
TheoremDoc Set.image_comp as "Set.image_comp" in "Set"

NewTheorem Set.image_comp

/-- `Set.image_image` states `f '' (g '' s) = (f ∘ g) '' s` — the
reversed form of `Set.image_comp`. Disabled to prevent one-shot
bypass of the nested destructuring lesson. -/
TheoremDoc Set.image_image as "Set.image_image" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_comp Set.image_image
