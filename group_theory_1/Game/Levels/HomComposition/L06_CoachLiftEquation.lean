import Game.Metadata

World "HomComposition"
Level 6

Title "Lifting an Equation Through Composition"

Introduction
"
If `f(a) = f(b)`, what can you say about `(g ∘ f)(a)` vs `(g ∘ f)(b)`?

Since `(g ∘ f)(a) = g(f(a))` and `(g ∘ f)(b) = g(f(b))`, and
`f(a) = f(b)`, we get `g(f(a)) = g(f(b))`, i.e.,
`(g ∘ f)(a) = (g ∘ f)(b)`.

This is the key step in the boss: to use injectivity of `g ∘ f`,
you need to produce an equation `(g ∘ f)(a) = (g ∘ f)(b)` from
`f(a) = f(b)`.
"

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (a b : G)
    (hab : f a = f b) : (g.comp f) a = (g.comp f) b := by
  Hint "Unfold both composition applications:
  `rw [MonoidHom.comp_apply, MonoidHom.comp_apply]`."
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  Hint "The goal is `g (f a) = g (f b)`. Substitute `{hab} : f a = f b`:
  `rw [{hab}]`."
  rw [hab]

Conclusion
"
From `f(a) = f(b)`, you derived `(g ∘ f)(a) = (g ∘ f)(b)` by
unfolding the composition and substituting.

This is the **lift-through-composition** step: if two inputs agree
after `f`, they agree after `g ∘ f` too. In the boss, you'll use
this in reverse: given `f(a) = f(b)`, lift to
`(g ∘ f)(a) = (g ∘ f)(b)`, then apply injectivity of `g ∘ f`
to conclude `a = b`.

On paper: *If `f(a) = f(b)`, then `g(f(a)) = g(f(b))`,
i.e., `(g ∘ f)(a) = (g ∘ f)(b)`.*
"
