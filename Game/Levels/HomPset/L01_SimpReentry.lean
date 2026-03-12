import Game.Metadata

World "HomPset"
Level 1

Title "Simplify a Conjugate"

Introduction
"
Welcome to the **Homomorphism Problem Set**.

You have all the tools from the last two worlds: `map_mul`, `map_one`,
`map_inv`, `simp`, `MonoidHom.mem_ker`, `MonoidHom.mem_range`, `specialize`,
`use`, `ext`, `mul_inv_eq_one`, and `Function.Injective`.

This first level is a warm-up: push `f` through a conjugation expression
using `simp`. From the next level onward, `simp` will be disabled.
"

TheoremTab "Hom"

DisabledTactic group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a⁻¹ * b * a) = (f a)⁻¹ * f b * f a := by
  Hint "Try `simp`. It will push `f` through `a⁻¹ * b * a` using
  `map_mul` and `map_inv` automatically."
  simp

Conclusion
"
`simp` pushed `f` through all three multiplications and the inverse
in one step. Under the hood it applied `map_mul` twice and `map_inv`
once.

The expression `a⁻¹ * b * a` is called a **conjugate** of `b` by `a`.
You'll see it again when you study normal subgroups — a subgroup is
normal precisely when it's closed under conjugation.

From the next level onward, `simp` is disabled: you'll work through
the algebra manually.
"
