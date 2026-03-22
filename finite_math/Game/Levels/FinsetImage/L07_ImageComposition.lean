import Game.Metadata

World "FinsetImage"
Level 7

Title "Image Respects Composition"

Introduction "
# The Algebraic Heart of Image

Applying $g$ then $f$ to a set gives the same result as applying
$f \\circ g$ directly:

$$(s.\\text{image}\\; g).\\text{image}\\; f \\;=\\; s.\\text{image}\\; (f \\circ g)$$

In FinTuples you proved that function composition is associative.
Now you'll see that **image respects composition**: applying two
functions in sequence to a set is the same as applying their
composition.

The proof uses `ext` and two layers of witness extraction:
- **Forward**: extract a witness from the outer image, then extract
  a deeper witness from the inner image
- **Backward**: extract a witness from the composed image, then
  build the two-layer membership

**Your task**: Prove the image-composition identity.

**Recall**: `Function.comp_apply` says `(f \\circ g) x = f (g x)`.
"

/-- Image respects function composition. -/
Statement (f g : ℕ → ℕ) (s : Finset ℕ) :
    (s.image g).image f = s.image (f ∘ g) := by
  Hint "Use `ext y` to reduce the equality to element-wise membership."
  ext y
  Hint "Split the biconditional with `constructor`."
  constructor
  -- Forward: y ∈ (s.image g).image f → y ∈ s.image (f ∘ g)
  · Hint "Extract the witness from the outer image, then extract the
    deeper witness from the inner image."
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨z, hz, hfz⟩ := h
    Hint "You have `z ∈ s.image g`. Extract the original element
    from `hz`."
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, hgx⟩ := hz
    Hint (hidden := true) "Now build `y ∈ s.image (f ∘ g)` with
    witness `x`. Use `rw [Finset.mem_image]` on the goal,
    then `exact ⟨x, hx, by rw [Function.comp_apply, hgx, hfz]⟩`."
    rw [Finset.mem_image]
    use x
    constructor
    · exact hx
    · rw [Function.comp_apply, hgx, hfz]
  -- Backward: y ∈ s.image (f ∘ g) → y ∈ (s.image g).image f
  · Hint "Extract the witness from the composed image, then build
    the two-layer membership."
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hfgx⟩ := h
    Hint (hidden := true) "Provide `g x` as the witness for the outer image.
    `rw [Finset.mem_image]`, `use g x`, then build `g x ∈ s.image g`
    with witness `x`, and show `f (g x) = y` from the composition."
    rw [Finset.mem_image]
    use g x
    constructor
    · rw [Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    · rw [Function.comp_apply] at hfgx
      exact hfgx

Conclusion "
You proved **image respects composition**:
$(s.\\text{image}\\; g).\\text{image}\\; f = s.\\text{image}\\; (f \\circ g)$

This is the fundamental algebraic property of image. Together with
Level 6 (image distributes over union), you've shown that image
is a **homomorphism**: it preserves both composition and union.

The forward direction used **two-layer extraction**: pulling a
witness from the outer image, then a deeper witness from the inner.
The backward direction used **two-layer construction**: building
membership in the inner image first, then wrapping it in the outer.

In Mathlib, this identity is `Finset.image_image`.
"

/-- `Finset.image_image` states that `(s.image f).image g = s.image (g ∘ f)`:
image respects function composition. -/
TheoremDoc Finset.image_image as "Finset.image_image" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.image_image
