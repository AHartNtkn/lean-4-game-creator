import Game.Metadata

World "HomComposition"
Level 7

Title "Boss — Injective Composition Implies Injective Inner Map"

Introduction
"
If `g ∘ f` is injective, then `f` must be injective.

Why? If `f(a) = f(b)`, then `g(f(a)) = g(f(b))`, so
`(g ∘ f)(a) = (g ∘ f)(b)`. Since `g ∘ f` is injective, `a = b`.

The proof combines:
- **intro** to unfold `Function.Injective` (Level 4)
- **comp_apply** to unfold the composition (Level 1)
- **rw** to lift through the composition (Level 6)
- **apply** with injectivity (Level 4)

Strategy:
1. Introduce `a`, `b`, and `hab : f a = f b`
2. Apply injectivity of `g ∘ f` to reduce to
   `(g.comp f) a = (g.comp f) b`
3. Unfold and substitute
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Function.Injective.of_comp as "Function.Injective.of_comp" in "Hom"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Function.Injective.of_comp_iff as "Function.Injective.of_comp_iff" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem Function.Injective.of_comp Function.Injective.of_comp_iff

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hgf : Function.Injective (g.comp f)) :
    Function.Injective f := by
  Hint "Start by unfolding injectivity. `Function.Injective f` means
  `∀ a b, f a = f b → a = b`.

  `intro a b hab`."
  intro a b hab
  Hint "You have `{hab} : f a = f b` and need to prove `a = b`.

  Since `{hgf} : Function.Injective (g.comp f)`, if you can show
  `(g.comp f) a = (g.comp f) b`, then `{hgf}` gives you `a = b`.

  Use `apply {hgf}` to reduce the goal."
  Branch
    -- One-liner: lift hab through g, then apply composition injectivity
    Hint (hidden := true) "You can close this in one step:
    `exact {hgf} (show (g.comp f) a = (g.comp f) b by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, {hab}])`."
    exact hgf (show (g.comp f) a = (g.comp f) b by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hab])
  apply hgf
  Hint "The goal is `(g.comp f) a = (g.comp f) b`. Unfold the
  composition: `rw [MonoidHom.comp_apply, MonoidHom.comp_apply]`."
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  Hint "The goal is `g (f a) = g (f b)`. Substitute `{hab}`:
  `rw [{hab}]`."
  rw [hab]

Conclusion
"
Congratulations on completing **Homomorphism Composition**!

You proved: **if `g ∘ f` is injective, then `f` is injective**.

The argument:
```
  f(a) = f(b)
  ⟹  g(f(a)) = g(f(b))        — apply g to both sides
  ⟹  (g ∘ f)(a) = (g ∘ f)(b)  — comp_apply
  ⟹  a = b                     — g ∘ f injective
```

Notice the contrapositive reading: if `f` collapsed two elements
(`f(a) = f(b)` with `a ≠ b`), then `g ∘ f` would also collapse them
(`(g ∘ f)(a) = (g ∘ f)(b)`). So if `g ∘ f` never collapses, `f`
never collapses either.

The converse is false: `g ∘ f` injective does NOT imply `g` is
injective. For example, let `f : ℤ → ℤ × ℤ` send `n ↦ (n, 0)`
and `g : ℤ × ℤ → ℤ` send `(a, b) ↦ a`. Then `g ∘ f` is the
identity (injective!), but `g` collapses `(0, 1)` and `(0, 0)`.

There's also a kernel-based proof of the boss: since
`ker(f) ≤ ker(g ∘ f)` (Level 2) and `ker(g ∘ f) = ⊥` (because
`g ∘ f` is injective), we get `ker(f) ≤ ⊥`, hence `ker(f) = ⊥`,
hence `f` is injective. This connects the first half of the world
(kernel/range containment) to the second half (injectivity/surjectivity
transfer).

This asymmetry — injectivity transfers to the **inner** map,
surjectivity transfers to the **outer** map — is the
**inner/outer transfer** pattern.

Summary of composition properties:

| Hypothesis | Conclusion | Why |
|------------|------------|-----|
| `f`, `g` injective | `g ∘ f` injective | Level 4: peel from outside |
| `g ∘ f` injective | `f` injective | Boss: lift and apply |
| `f`, `g` surjective | `g ∘ f` surjective | Dual of Level 4 |
| `g ∘ f` surjective | `g` surjective | Level 5: use `f(x)` as witness |
| `ker(f) ≤ ker(g ∘ f)` | — | Level 2: composition kills more |
| `range(g ∘ f) ≤ range(g)` | — | Level 3: composition reaches less |

Your tools from this world:

| Item | Type | Purpose |
|------|------|---------|
| `g.comp f` | Definition | Composition homomorphism `G →* K` |
| `MonoidHom.comp_apply` | Theorem | `(g.comp f) x = g (f x)` |

Proof moves:
- **Composition unfolding**: `rw [comp_apply]` to access inner structure
- **Lift through composition**: from `f(a) = f(b)`, derive `(g∘f)(a) = (g∘f)(b)`
- **Injectivity transfer**: `apply hgf` to use composition injectivity

On paper: *If `f(a) = f(b)`, then `g(f(a)) = g(f(b))`, so
`(g ∘ f)(a) = (g ∘ f)(b)`. Since `g ∘ f` is injective, `a = b`.
Therefore `f` is injective.*

Looking ahead: you'll next study how homomorphisms interact with
subgroups — images and preimages of subgroups under homomorphisms.
Later, these composition results will be essential when proving that
the first isomorphism theorem's map is well-defined and injective.
"
