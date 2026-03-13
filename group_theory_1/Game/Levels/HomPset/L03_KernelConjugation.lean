import Game.Metadata

World "HomPset"
Level 3

Title "Kernel Absorbs Conjugation"

Introduction
"
If `a` is in the kernel of `f`, what about `b * a * b⁻¹`?

Since `f(a) = 1`:

`f(b * a * b⁻¹) = f(b) · f(a) · f(b)⁻¹ = f(b) · 1 · f(b)⁻¹ = 1`

So `b * a * b⁻¹ ∈ ker(f)` too. The kernel \"absorbs\" conjugation.

The proof combines kernel reasoning (unfold `mem_ker`) with the
hom-property move (push `f` through the expression).
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.normal_ker Subgroup.Normal.conj_mem Subgroup.Normal.conj_mem'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G)
    (ha : a ∈ f.ker) : b * a * b⁻¹ ∈ f.ker := by
  Hint "Unfold `{ha}` and the goal using `MonoidHom.mem_ker`:
  `rw [MonoidHom.mem_ker] at {ha}`."
  rw [MonoidHom.mem_ker] at ha
  Hint "Now unfold the goal: `rw [MonoidHom.mem_ker]`."
  rw [MonoidHom.mem_ker]
  Hint "Push `f` through `b * a * b⁻¹`. You need two `map_mul` rewrites
  (for `(b * a) * b⁻¹` and `b * a`) and one `map_inv`.

  Try `rw [map_mul, map_mul, map_inv]`."
  rw [map_mul, map_mul, map_inv]
  Hint "The goal is `f b * f a * (f b)⁻¹ = 1`. Substitute `{ha} : f a = 1`:
  `rw [{ha}]`."
  rw [ha]
  Hint (hidden := true) "The goal is `f b * 1 * (f b)⁻¹ = 1`. Use
  `rw [mul_one]` then `exact mul_inv_cancel (f b)`."
  rw [mul_one]
  exact mul_inv_cancel (f b)

Conclusion
"
The kernel is closed under conjugation: if `a ∈ ker(f)`, then
`bab⁻¹ ∈ ker(f)` for every `b ∈ G`.

A subgroup with this property is called **normal**. You'll prove
formally that every kernel is normal later in the course. For now,
notice the proof pattern:

1. Unfold `mem_ker` at hypothesis and goal
2. Push `f` through the expression (`map_mul`, `map_inv`)
3. Substitute the kernel equation (`f a = 1`)
4. Simplify the group algebra

On paper: *Since `f(a) = 1`, we have
`f(bab⁻¹) = f(b)f(a)f(b)⁻¹ = f(b) · 1 · f(b)⁻¹ = 1`,
so `bab⁻¹ ∈ ker(f)`.*
"
