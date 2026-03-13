import Game.Metadata

World "HomComposition"
Level 3

Title "Range Containment"

Introduction
"
The range of `g ∘ f` is contained in the range of `g`.

Why? Every output of `g ∘ f` has the form `g(f(x))`. But `g(f(x))` is
also an output of `g` (with input `f(x)`). So everything `g ∘ f`
reaches, `g` also reaches.

The proof uses the **image-reasoning move** from Kernel and Image:
unfold `mem_range`, extract the witness, then provide a new witness.
"

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (y : K)
    (hy : y ∈ (g.comp f).range) : y ∈ g.range := by
  Hint "Unfold range membership in the hypothesis:
  `rw [MonoidHom.mem_range] at {hy}`."
  rw [MonoidHom.mem_range] at hy
  Hint "Now `{hy} : ∃ x, (g.comp f) x = y`. Extract the witness:
  `obtain ⟨x, hx⟩ := {hy}`."
  obtain ⟨x, hx⟩ := hy
  Hint "You have `hx : (g.comp f) x = y`. Unfold range membership in
  the goal: `rw [MonoidHom.mem_range]`."
  rw [MonoidHom.mem_range]
  Hint "The goal is `∃ x_1, g x_1 = y`. You need an element of `H`
  that `g` maps to `y`. Since `(g.comp f)(x) = g(f(x)) = y`, the
  element `f x` works.

  Provide the witness: `use f x`."
  use f x
  Hint "The goal is `g (f x) = y`. Rewrite using `comp_apply`:
  `rw [← MonoidHom.comp_apply]`."
  Branch
    -- Alternative: exact hx works directly (definitional equality)
    Hint (hidden := true) "The goal `g (f x) = y` is definitionally
    equal to `(g.comp f) x = y`, so `exact hx` closes it directly."
    exact hx
  rw [← MonoidHom.comp_apply]
  Hint (hidden := true) "Now `exact hx`."
  exact hx

Conclusion
"
The argument:
1. `y ∈ range(g ∘ f)` means `∃ x, (g ∘ f)(x) = y`
2. Extract the witness: `(g ∘ f)(x) = g(f(x)) = y`
3. So `f(x) ∈ H` is a preimage of `y` under `g`
4. Therefore `y ∈ range(g)`

This proves `range(g ∘ f) ≤ range(g)`: the composition can only
reach things that `g` can reach. The composition might reach *fewer*
things, because `g` might be able to reach outputs that aren't of
the form `g(f(x))`.

Contrast the two containments:

| Containment | Direction | Reason |
|-------------|-----------|--------|
| `ker(f) ≤ ker(g ∘ f)` | Kernel grows | Composition kills more |
| `range(g ∘ f) ≤ range(g)` | Range shrinks | Composition reaches less |

Together with Level 2, the dual containments say: **composition is
lossy — kernels grow, ranges shrink**. Composing `f` then `g` can
only destroy more information (enlarging the kernel) and reach fewer
outputs (shrinking the range).

On paper: *If `y = (g ∘ f)(x) = g(f(x))`, then `y` is in the range
of `g` (witnessed by `f(x)`).*
"
