import Game.Metadata

World "ImageWorld"
Level 9

Title "Seeing the Intersection Gap"

TheoremTab "Set"

Introduction "
# A Counterexample: Image Does NOT Preserve Intersection

In Level 8, you proved `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` and read
about why equality can fail. Now you will SEE it fail.

Consider the **constant function** `f(n) = 0` (sending every natural
number to 0), with `s = {0}` and `t = {1}`:

- `s ∩ t = ∅` (0 ≠ 1, so nothing is in both)
- `f '' (s ∩ t) = f '' ∅ = ∅`
- But `f '' s = {0}` and `f '' t = {0}`, so `f '' s ∩ f '' t = {0}`

The element `0` is in `f '' s ∩ f '' t` (witnessed by `0 ∈ s` and
`1 ∈ t` -- DIFFERENT witnesses!) but NOT in `f '' (s ∩ t)` (because
`s ∩ t` is empty).

**Your task**: Prove BOTH facts:
1. `0 ∈ f '' s ∩ f '' t` (the intersection of images is nonempty)
2. `0 ∉ f '' (s ∩ t)` (the image of intersection IS empty)

This is a concrete demonstration that the ⊆ in Level 8 is STRICT.
"

/-- The constant function demonstrates that image of intersection
can be strictly smaller than intersection of images. -/
Statement : (0 : ℕ) ∈ (fun _ : ℕ => (0 : ℕ)) '' {n | n = 0} ∩
    (fun _ : ℕ => (0 : ℕ)) '' {n | n = 1} ∧
    (0 : ℕ) ∉ (fun _ : ℕ => (0 : ℕ)) '' ({n | n = 0} ∩ {n | n = 1}) := by
  Hint "Use `constructor` to split into the two parts."
  constructor
  -- Part 1: 0 ∈ f '' s ∩ f '' t
  · Hint "The goal is a conjunction (intersection membership). Use
    `constructor` again to split into `0 ∈ f '' s` and `0 ∈ f '' t`."
    constructor
    · Hint "Prove `0 ∈ (fun _ => 0) '' ...` by providing a witness.
      The witness for `f '' (n | n = 0)` is `n = 0`."
      Hint (hidden := true) "`exact ⟨0, rfl, rfl⟩` -- witness 0, membership
      `0 = 0`, and equation `f 0 = 0`."
      exact ⟨0, rfl, rfl⟩
    · Hint "Now prove `0 ∈ (fun _ => 0) '' (n | n = 1)`. The witness
      here is `n = 1` -- a DIFFERENT element than before!"
      Hint (hidden := true) "`exact ⟨1, rfl, rfl⟩` -- witness 1, membership
      `1 = 1`, and equation `f 1 = 0`."
      exact ⟨1, rfl, rfl⟩
  -- Part 2: 0 ∉ f '' (s ∩ t)
  · Hint "The goal is `0 ∉ f '' (... ∩ ...)`, which means
    `0 ∈ f '' (... ∩ ...) → False`.

    Use `rintro ⟨x, ⟨hx0, hx1⟩, _⟩` to assume it IS in the image
    and destructure: `x` is the witness, `hx0 : x ∈ (n | n = 0)` and
    `hx1 : x ∈ (n | n = 1)`."
    Hint (hidden := true) "After destructuring, `hx0` is definitionally
    `x = 0` and `hx1` is definitionally `x = 1`. Extract with
    `have h0 : x = 0 := hx0` and `have h1 : x = 1 := hx1`, then `omega`."
    rintro ⟨x, ⟨hx0, hx1⟩, _⟩
    Hint "You have `hx0 : x ∈ (n | n = 0)` (which is `x = 0`) and
    `hx1 : x ∈ (n | n = 1)` (which is `x = 1`). These are
    contradictory! Extract the equalities with `have`."
    Hint (hidden := true) "`have h0 : x = 0 := hx0` then
    `have h1 : x = 1 := hx1` then `omega`."
    have h0 : x = 0 := hx0
    have h1 : x = 1 := hx1
    omega

Conclusion "
You have now SEEN the intersection gap in action!

The key observation: `0 ∈ f '' s ∩ f '' t` has TWO DIFFERENT witnesses:
- `0 ∈ s` witnesses `0 ∈ f '' s`
- `1 ∈ t` witnesses `0 ∈ f '' t`

But `0 ∉ f '' (s ∩ t)` because ANY single witness would need to be
in BOTH `s` and `t` -- and `s ∩ t` is empty.

**The root cause**: The constant function collapses `0` and `1` to
the same output. The intersection of images uses different witnesses
for the same output, while the image of intersection demands a single
witness that works for both sets.

**The injectivity connection**: If `f` were injective, the two
witnesses would have to be equal (since `f x₁ = f x₂ = 0` would
imply `x₁ = x₂`). So injectivity prevents this kind of phantom
intersection. You will prove `f '' (s ∩ t) = f '' s ∩ f '' t` for
injective `f` in a later world.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
