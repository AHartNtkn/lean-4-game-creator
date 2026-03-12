import Game.Metadata

World "HomDef"
Level 8

Title "Boss — Into the Kernel"

Introduction
"
Final challenge: combine everything you've learned.

Given a homomorphism `f : G →* H` and two elements with
`h : f a = f b`, prove that `f (a * b⁻¹) = 1`.

Mathematically: if `f` sends `a` and `b` to the same element,
then `f` sends their \"ratio\" `a * b⁻¹` to the identity.

You have two strategies:

**Manual** (4 steps):
1. Push `f` through `a * b⁻¹` using `map_mul` and `map_inv`
2. Use `h` to substitute `f a` with `f b`
3. Cancel `f b * (f b)⁻¹`

**Automatic**: `simp [h]`
"

TheoremTab "Hom"

DisabledTactic group

/-- Disabled — decompose using `map_mul` and `map_inv` separately. -/
TheoremDoc map_mul_inv as "map_mul_inv" in "Hom"

DisabledTheorem map_mul_inv

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G)
    (h : f a = f b) : f (a * b⁻¹) = 1 := by
  Hint "Start by pushing `f` through the product:
  `rw [map_mul]` splits `f (a * b⁻¹)` into `f a * f b⁻¹`."
  Branch
    simp [h]
  rw [map_mul]
  Hint "Now push `f` through the inverse:
  `rw [map_inv]` converts `f b⁻¹` to `(f b)⁻¹`."
  rw [map_inv]
  Hint "The goal is `f a * (f b)⁻¹ = 1`. You know `f a = f b`
  from hypothesis `{h}`. Use `rw [{h}]` to substitute."
  rw [h]
  Hint (hidden := true) "The goal is `f b * (f b)⁻¹ = 1`.
  Use `exact mul_inv_cancel (f b)`."
  exact mul_inv_cancel (f b)

Conclusion
"
Congratulations on completing **Homomorphisms**!

You proved: if `f(a) = f(b)`, then `f(a · b⁻¹) = 1`. This is the
embryonic form of **kernel reasoning**.

The **kernel** of `f` is the set `{x ∈ G | f(x) = 1}`. What you
just showed is that `a · b⁻¹ ∈ ker(f)` whenever `f(a) = f(b)`.

A homomorphism with trivial kernel — `ker(f) = {1}` — sends distinct
elements to distinct elements: it is *injective*. In the next world,
you'll formalize the kernel and prove this equivalence.

Your new tools from this world:

| Item | Type | Purpose |
|------|------|---------|
| `simp` | Tactic | Automated simplification using tagged lemmas |
| `simp [h]` | Tactic | Directed simplification including hypothesis `h` |
| `G →* H` | Notation | Group homomorphism (MonoidHom) |
| `map_mul f a b` | Theorem | `f (a * b) = f a * f b` |
| `map_one f` | Theorem | `f 1 = 1` |
| `map_inv f a` | Theorem | `f a⁻¹ = (f a)⁻¹` |
| `MonoidHom.mk_fun` | Theorem | Construct a hom by proving `map_mul` |

The **hom-property move**: push `f` through group operations
using `map_mul`, `map_one`, `map_inv` (or `simp`), then simplify.

On paper: *\"Since `f(a) = f(b)`, we have
`f(ab⁻¹) = f(a)f(b⁻¹) = f(a)f(b)⁻¹ = f(b)f(b)⁻¹ = 1`.\"*
"
