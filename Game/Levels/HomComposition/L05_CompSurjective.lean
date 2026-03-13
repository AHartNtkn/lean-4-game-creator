import Game.Metadata

World "HomComposition"
Level 5

Title "Surjective Composition Implies Surjective Outer Map"

Introduction
"
If `g ∘ f` is surjective, what can you conclude about `g`?

`g` must be surjective too. For any `y ∈ K`, surjectivity of `g ∘ f`
gives some `x ∈ G` with `(g ∘ f)(x) = y`, i.e., `g(f(x)) = y`. So
`f(x) ∈ H` is a preimage of `y` under `g`.

This is the surjectivity dual of the boss theorem. The boss says:
`g ∘ f` injective → `f` injective. Here: `g ∘ f` surjective → `g`
surjective. Notice the asymmetry: injectivity transfers to `f` (the
inner map), surjectivity transfers to `g` (the outer map).
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Function.Surjective.of_comp as "Function.Surjective.of_comp" in "Hom"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Function.Surjective.of_comp_iff as "Function.Surjective.of_comp_iff" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem Function.Surjective.of_comp Function.Surjective.of_comp_iff

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hgf : Function.Surjective (g.comp f)) :
    Function.Surjective g := by
  Hint "`Function.Surjective g` means `∀ y, ∃ x, g x = y`.
  Introduce the target element: `intro y`."
  intro y
  Hint "You need `∃ x, g x = y`. Since `g ∘ f` is surjective, there
  exists some `x : G` with `(g ∘ f)(x) = y`.

  Apply the surjectivity hypothesis: `obtain ⟨x, hx⟩ := {hgf} y`."
  obtain ⟨x, hx⟩ := hgf y
  Hint "You have `hx : (g.comp f) x = y`. You need `∃ x_1, g x_1 = y`.

  Provide the witness `f x`: `use f x`."
  use f x
  Hint "The goal is `g (f x) = y`. Rewrite using `comp_apply`:
  `rw [← MonoidHom.comp_apply]`."
  rw [← MonoidHom.comp_apply]
  Hint (hidden := true) "Now `exact hx`."
  exact hx

Conclusion
"
If `g ∘ f` is surjective, then `g` is surjective. The argument:
for any `y ∈ K`, surjectivity of `g ∘ f` gives `x` with
`g(f(x)) = y`, so `f(x)` is a preimage of `y` under `g`.

The duality between the boss theorem and this result:

| Hypothesis | Conclusion | Transfers to |
|------------|------------|--------------|
| `g ∘ f` injective | `f` injective | inner map |
| `g ∘ f` surjective | `g` surjective | outer map |

Why the asymmetry? Think of it as a pipeline `G → H → K`:
- If nothing collides at the end (injective composition), nothing
  can collide at the start (injective `f`). But `g` might still
  collide on elements outside `range(f)`.
- If everything is reached at the end (surjective composition),
  everything is reached by the second step (surjective `g`). But
  `f` might miss parts of `H` that `g` still covers.

This is the **inner/outer transfer** pattern:

| Hypothesis | Conclusion | Transfers to |
|------------|------------|--------------|
| `g ∘ f` injective | `f` injective | inner map |
| `g ∘ f` surjective | `g` surjective | outer map |

Think of `G →f→ H →g→ K` as a pipeline. If the pipeline never
collides (injective), the first step can't collide either. If the
pipeline reaches everything (surjective), the second step reaches
everything too.

On paper: *For any `y ∈ K`, surjectivity of `g ∘ f` gives `x ∈ G`
with `g(f(x)) = y`. So `f(x) ∈ H` is a preimage of `y` under `g`,
proving `g` surjective.*
"
