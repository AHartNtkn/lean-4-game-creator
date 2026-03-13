import Game.Metadata

World "NormalDef"
Level 6

Title "Kernel Absorbs Conjugation"

Introduction
"
You proved in the homomorphism problem set that `b * a * b⁻¹ ∈ ker(f)`
whenever `a ∈ ker(f)`. Now prove the \"other side\" variant:
`b⁻¹ * a * b ∈ ker(f)`.

You just learned in Level 3 that `conj_mem'` gives conjugation by the
*inverse*. But here you won't use normality at all — you'll prove it
directly from `mem_ker` and the homomorphism property, combining the
`have` + `inv_inv` trick from Level 3 with kernel reasoning.
"

/-- Disabled — you will prove this yourself in the boss. -/
TheoremDoc MonoidHom.normal_ker as "MonoidHom.normal_ker" in "Normal"

/-- Disabled — proves `g⁻¹ * n * g ∈ N` directly. -/
TheoremDoc Subgroup.Normal.conj_mem' as "conj_mem'" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem MonoidHom.normal_ker Subgroup.Normal.conj_mem Subgroup.Normal.conj_mem'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G)
    (ha : a ∈ f.ker) : b⁻¹ * a * b ∈ f.ker := by
  Hint "Unfold kernel membership at hypothesis and goal:
  `rw [MonoidHom.mem_ker] at {ha} ⊢`."
  rw [MonoidHom.mem_ker] at ha ⊢
  Hint "Push `f` through `b⁻¹ * a * b`: `rw [map_mul, map_mul, map_inv]`."
  rw [map_mul, map_mul, map_inv]
  Hint "Substitute `{ha} : f a = 1`: `rw [{ha}]`."
  rw [ha]
  Hint (hidden := true) "The goal is `(f b)⁻¹ * 1 * f b = 1`.
  `rw [mul_one]` then `exact inv_mul_cancel (f b)`."
  rw [mul_one]
  exact inv_mul_cancel (f b)

Conclusion
"
The kernel absorbs conjugation from *both sides*: if `a ∈ ker(f)`, then
both `b * a * b⁻¹` and `b⁻¹ * a * b` are in `ker(f)`.

The proof follows the same pattern as the problem set version:

1. Unfold `mem_ker` (hypothesis and goal)
2. Push `f` through (`map_mul`, `map_inv`)
3. Substitute `f(a) = 1`
4. Cancel

On paper: *`f(b⁻¹ab) = f(b)⁻¹ · f(a) · f(b) = f(b)⁻¹ · 1 · f(b) = 1`,
so `b⁻¹ab ∈ ker(f)`.*

In the boss, you'll package this kind of argument into a formal proof
that `f.ker.Normal`.
"
