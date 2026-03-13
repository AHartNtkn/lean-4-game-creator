import Game.Metadata

World "HomComposition"
Level 4

Title "Composition of Injective Homomorphisms"

Introduction
"
If `f` is injective and `g` is injective, is `g ∘ f` injective?

Yes: if `(g ∘ f)(a) = (g ∘ f)(b)`, then `g(f(a)) = g(f(b))`. Since
`g` is injective, `f(a) = f(b)`. Since `f` is injective, `a = b`.

The proof chains two applications of injectivity. You'll need
`comp_apply` to unfold the composition, then `apply` each
injectivity hypothesis.
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Function.Injective.comp as "Function.Injective.comp" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem Function.Injective.comp

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g.comp f) := by
  Hint "Start by introducing the elements and the hypothesis.
  `Function.Injective (g.comp f)` means `∀ a b, (g.comp f) a = (g.comp f) b → a = b`.

  `intro a b hab`."
  intro a b hab
  Hint "Unfold the composition in `{hab}`:
  `rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at {hab}`."
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hab
  Hint "Now `{hab} : g (f a) = g (f b)`. Since `g` is injective,
  `g(f(a)) = g(f(b))` implies `f(a) = f(b)`.

  Use `apply {hf}` to reduce the goal `a = b` to `f a = f b`."
  apply hf
  Hint "The goal is `f a = f b`. Since `g` is injective and
  `{hab} : g (f a) = g (f b)`, apply injectivity of `g`:
  `exact {hg} {hab}`."
  exact hg hab

Conclusion
"
The chain of injectivity:
```
(g ∘ f)(a) = (g ∘ f)(b)
  ⟹  g(f(a)) = g(f(b))    — comp_apply
  ⟹  f(a) = f(b)           — g injective
  ⟹  a = b                 — f injective
```

This proves: **the composition of injective homomorphisms is injective**.

The proof peels the onion from the outside in: first remove `g` using
its injectivity, then remove `f` using its injectivity.

Notice the Lean pattern: `apply hf` reduces the goal to showing
`f a = f b`, and then `exact hg hab` uses `g`'s injectivity on
the hypothesis `g(f(a)) = g(f(b))` to get `f(a) = f(b)`.

On paper: *If `g(f(a)) = g(f(b))`, then `f(a) = f(b)` since `g` is
injective, and then `a = b` since `f` is injective.*
"
