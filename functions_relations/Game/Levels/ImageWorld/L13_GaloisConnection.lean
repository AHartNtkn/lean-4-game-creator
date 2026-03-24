import Game.Metadata

World "ImageWorld"
Level 13

Title "The Galois Connection"

TheoremTab "Set"

Introduction "
# Image-Subset ↔ Subset-Preimage

Here is one of the most useful equivalences connecting image and
preimage:

$$f(s) \\subseteq t \\;\\;\\Longleftrightarrow\\;\\; s \\subseteq f^{-1}(t)$$

This says: \"the image of `s` fits inside `t`\" is the same as
\"every element of `s` maps into `t`.\" Both viewpoints describe
the same condition, but the preimage viewpoint is often easier to
work with (because preimage membership is just function application).

This equivalence is called a **Galois connection** between image
and preimage. It is the fundamental bridge connecting the two
operations.

**Proof plan**:
1. `constructor` to split the `↔`
2. **Forward** (`f '' s ⊆ t → s ⊆ f ⁻¹' t`): Take `x ∈ s`, apply
   `h` to `f x ∈ f '' s`, get `f x ∈ t` (which is `x ∈ f ⁻¹' t`)
3. **Backward** (`s ⊆ f ⁻¹' t → f '' s ⊆ t`): Take `y ∈ f '' s`,
   destructure to get `x ∈ s`, apply `h` to get `f x ∈ t`
"

/-- The Galois connection between image and preimage. -/
Statement (α β : Type) (f : α → β) (s : Set α) (t : Set β) :
    f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  Hint "Use `constructor` to split the biconditional."
  constructor
  -- Forward: f '' s ⊆ t → s ⊆ f ⁻¹' t
  · Hint "**Forward**: Assume `h : f '' s ⊆ t`. You need to show
    `s ⊆ f ⁻¹' t`, which means: for every `x ∈ s`, prove `x ∈ f ⁻¹' t`
    (i.e., `f x ∈ t`).

    Use `intro h x hx`."
    Hint (hidden := true) "After `intro h x hx`, use `apply h` to reduce
    the goal to `f x ∈ f '' s`, then `exact ⟨x, hx, rfl⟩`."
    intro h x hx
    Hint "The goal is `x ∈ f ⁻¹' t`, which is definitionally `f x ∈ t`.
    You know `h : f '' s ⊆ t`, so if you can show `f x ∈ f '' s`,
    then `h` will give you `f x ∈ t`.

    Use `apply h` to reduce the goal to `f x ∈ f '' s`."
    Hint (hidden := true) "`apply h` then `exact ⟨x, hx, rfl⟩`.

    Or in one step: `exact h ⟨x, hx, rfl⟩`."
    Branch
      exact h ⟨x, hx, rfl⟩
    apply h
    Hint "Now prove `f x ∈ f '' s`. The witness is `x` with `hx : x ∈ s`."
    exact ⟨x, hx, rfl⟩
  -- Backward: s ⊆ f ⁻¹' t → f '' s ⊆ t
  · Hint "**Backward**: Assume `h : s ⊆ f ⁻¹' t`. You need to show
    `f '' s ⊆ t`. Use `intro y hy` then destructure `hy`."
    Hint (hidden := true) "After destructuring `hy` with
    `obtain ⟨x, hx, rfl⟩ := hy`, the goal becomes `f x ∈ t`.
    Then `exact h hx`."
    intro h y hy
    Hint "Destructure `hy : y ∈ f '' s` with
    `obtain ⟨x, hx, rfl⟩ := hy`."
    obtain ⟨x, hx, rfl⟩ := hy
    Hint "Now `hx : x ∈ s` and the goal is `f x ∈ t`.
    Since `h : s ⊆ f ⁻¹' t`, we have `h hx : x ∈ f ⁻¹' t`,
    which is definitionally `f x ∈ t`."
    Hint (hidden := true) "`exact h hx`"
    exact h hx

Conclusion "
You proved `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t` -- the Galois connection!

**Why this matters**: The Galois connection lets you switch between
two viewpoints:
- **Image viewpoint**: \"every output from `s` lands in `t`\"
- **Preimage viewpoint**: \"every element of `s` maps into `t`\"

The preimage viewpoint is often simpler because preimage membership
is just `f x ∈ t` -- no existential, no witness. So when you need
to prove `f '' s ⊆ t`, you can rewrite with `Set.image_subset_iff`
to get the easier goal `s ⊆ f ⁻¹' t`.

**The proof structure**:
- **Forward**: Start with `x ∈ s`, build `f x ∈ f '' s` (construct
  the witness `⟨x, hx, rfl⟩`), then apply the subset hypothesis
- **Backward**: Start with `y ∈ f '' s`, destructure to get `x ∈ s`,
  then apply the subset hypothesis directly (no construction needed!)

The backward direction is shorter because preimage is simpler than image.

**The general definition**: Two monotone functions `L : P → Q` and
`R : Q → P` between ordered sets form a **Galois connection** when
`L a ≤ b ↔ a ≤ R b` for all `a, b`. Here `L = f ''` (image) and
`R = f ⁻¹'` (preimage), with `⊆` as the order. This pattern appears
whenever two operations are \"adjoint\" to each other -- you will
study Galois connections formally in Orders and Lattices.

The library name is `Set.image_subset_iff`.
"

/-- `Set.image_subset_iff` states `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`.
This is the Galois connection between image and preimage: the image
of `s` fits inside `t` if and only if `s` is contained in the
preimage of `t`.

## Syntax
```
rw [Set.image_subset_iff]    -- convert f '' s ⊆ t to s ⊆ f ⁻¹' t
```

## When to use it
When you have a goal of the form `f '' s ⊆ t` and want to work with
the simpler preimage form `s ⊆ f ⁻¹' t` instead.
-/
TheoremDoc Set.image_subset_iff as "Set.image_subset_iff" in "Set"

NewTheorem Set.image_subset_iff

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_subset_iff Iff.rfl
