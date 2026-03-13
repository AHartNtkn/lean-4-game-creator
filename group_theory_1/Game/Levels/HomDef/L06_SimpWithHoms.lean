import Game.Metadata

World "HomDef"
Level 6

Title "Simplifying Homomorphism Expressions"

Introduction
"
You've learned three lemmas: `map_mul`, `map_one`, `map_inv`. Each
pushes `f` through one group operation.

When an expression has multiple operations inside `f`, you *could*
apply each lemma manually — but `simp` handles them all at once.
The lemmas `map_mul`, `map_one`, and `map_inv` are all tagged
`@[simp]` in Mathlib, so `simp` uses them automatically.

This is the **hom-property move**: push `f` through the expression,
then simplify.
"

TheoremTab "Hom"

DisabledTactic group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b⁻¹ * 1) = f a * (f b)⁻¹ := by
  Hint "You could apply `map_mul`, `map_inv`, `map_one`, and `mul_one`
  step by step. Or let `simp` handle it all: try `simp`."
  Branch
    rw [mul_one, map_mul, map_inv]
  simp

Conclusion
"
`simp` pushed `f` through all the operations and simplified
the result — all in one step.

Under the hood, `simp` applied:
1. `mul_one` to simplify `b⁻¹ * 1` to `b⁻¹`
2. `map_mul` to split `f (a * b⁻¹)` into `f a * f b⁻¹`
3. `map_inv` to convert `f b⁻¹` to `(f b)⁻¹`

The manual proof `rw [mul_one, map_mul, map_inv]` does the same
thing explicitly.

This \"push the hom through, then simplify\" pattern is the
**hom-property move** — the fundamental technique for working
with homomorphisms.
"
