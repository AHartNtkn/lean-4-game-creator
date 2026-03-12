import Game.Metadata

World "HomDef"
Level 5

Title "Homomorphisms Preserve Inverses"

Introduction
"
The final member of the hom-property family: `map_inv`.

`map_inv f a : f a⁻¹ = (f a)⁻¹`

Like `map_one`, this is a *consequence* of `map_mul` — not an extra
axiom. The derivation: from `f(a) · f(a⁻¹) = f(a · a⁻¹) = f(1) = 1`,
we conclude `f(a⁻¹) = f(a)⁻¹` by uniqueness of inverses.

Prove that `f a * f a⁻¹ = 1` using `map_inv`. Or, if you're feeling
ambitious, try deriving it from `map_mul` and `map_one` alone:
`rw [← map_mul, mul_inv_cancel, map_one]`.
"

/-- `map_inv` says: for any group homomorphism `f : G →* H`,

`f a⁻¹ = (f a)⁻¹`

A homomorphism sends inverses to inverses. This is a consequence
of `map_mul` and `map_one` (not an extra axiom).

Use `rw [map_inv]` to rewrite `f a⁻¹` to `(f a)⁻¹`. -/
TheoremDoc map_inv as "map_inv" in "Hom"

NewTheorem map_inv

TheoremTab "Hom"

DisabledTactic group simp

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a : G) :
    f a * f a⁻¹ = 1 := by
  Hint "Use `rw [map_inv]` to convert `f a⁻¹` to `(f a)⁻¹`."
  Branch
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_inv]
  Hint (hidden := true) "The goal is now `f a * (f a)⁻¹ = 1`. Use
  `exact mul_inv_cancel (f a)`."
  exact mul_inv_cancel (f a)

Conclusion
"
Together, `map_mul`, `map_one`, and `map_inv` say that a homomorphism
\"commutes\" with all group operations:

| Lemma | Statement |
|-------|-----------|
| `map_mul f a b` | `f (a * b) = f a * f b` |
| `map_one f` | `f 1 = 1` |
| `map_inv f a` | `f a⁻¹ = (f a)⁻¹` |

The key insight: only `map_mul` is an axiom. `map_one` and `map_inv`
are *consequences*. If you tried the alternative proof
`rw [← map_mul, mul_inv_cancel, map_one]`, you derived the result
using only `map_mul` and `map_one` — the same **hom-property move**
you used in the last level.

Some concrete examples of homomorphisms:
- The **identity map** `id : G →* G` (sends every element to itself)
- The **trivial map** `G →* H` sending every element to `1`
- The **squaring map** in a commutative group (you'll build this soon)

The trivial map sends *everything* to `1`, so its kernel is all of `G` —
the maximally non-injective case. You'll explore kernels in the next world.
"
