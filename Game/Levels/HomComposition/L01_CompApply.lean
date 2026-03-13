import Game.Metadata

World "HomComposition"
Level 1

Title "Composing Homomorphisms"

Introduction
"
Given two group homomorphisms `f : G →* H` and `g : H →* K`, their
**composition** `g.comp f` is a new homomorphism `G →* K` that first
applies `f`, then applies `g`.

The key unfolding lemma is `MonoidHom.comp_apply`:

`MonoidHom.comp_apply : (g.comp f) x = g (f x)`

Use `rw [MonoidHom.comp_apply]` to unfold `(g.comp f) x` into `g (f x)`.

Since `g.comp f` is a homomorphism, it respects multiplication: it sends
products to products. Verify this by computing `(g.comp f)(a * b)`.
"

/-- The composition of two group homomorphisms.

If `f : G →* H` and `g : H →* K`, then `g.comp f : G →* K`
is the homomorphism that maps `x` to `g(f(x))`.

Use `MonoidHom.comp_apply` to unfold: `(g.comp f) x = g (f x)`. -/
DefinitionDoc MonoidHom.comp as "MonoidHom.comp"

NewDefinition MonoidHom.comp

/-- `MonoidHom.comp_apply` says: for group homomorphisms
`f : G →* H` and `g : H →* K`,

`(g.comp f) x = g (f x)`

Use `rw [MonoidHom.comp_apply]` to unfold a composition
application into nested function applications. -/
TheoremDoc MonoidHom.comp_apply as "MonoidHom.comp_apply" in "Hom"

NewTheorem MonoidHom.comp_apply

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (a b : G) :
    (g.comp f) (a * b) = g (f a) * g (f b) := by
  Hint "The left side is `(g.comp f) (a * b)`. Unfold the composition:
  `rw [MonoidHom.comp_apply]`."
  rw [MonoidHom.comp_apply]
  Hint "The goal is `g (f (a * b)) = g (f a) * g (f b)`. Push `f` through
  the product first: `rw [map_mul]`."
  rw [map_mul]
  Hint "Now push `g` through: `rw [map_mul]`."
  rw [map_mul]

Conclusion
"
The computation:
```
(g.comp f)(a * b) = g(f(a * b))        — comp_apply
                  = g(f(a) * f(b))      — f is a hom (map_mul)
                  = g(f(a)) * g(f(b))   — g is a hom (map_mul)
```

The pattern is always: unfold `comp_apply`, then push each
homomorphism through using `map_mul` (or `map_inv`, `map_one`).

This is really the **hom-property move applied twice** — once for `f`,
once for `g`. Since `g.comp f` is itself a homomorphism, you could also
have used `map_mul` directly on `g.comp f`. But understanding the
two-step unfolding is essential for reasoning about kernels and
images of compositions.

On paper: *`(g ∘ f)(ab) = g(f(ab)) = g(f(a)f(b)) = g(f(a)) · g(f(b))`.*
"
