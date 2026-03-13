import Game.Metadata

World "NormalDef"
Level 8

Title "Two-Element Kernel Conjugation"

Introduction
"
Given two elements `a, b ∈ ker(f)`, prove that `g * (a * b) * g⁻¹`
is also in the kernel.

One approach: unfold everything and push `f` through the entire
expression. But there's a cleaner strategy — use `have` to first
combine `a` and `b` into a single kernel element, then do the
conjugation.

The `have` tactic lets you build the proof in stages rather than
one long chain.
"

/-- Disabled — you will prove this in the boss. -/
TheoremDoc MonoidHom.normal_ker as "MonoidHom.normal_ker" in "Normal"

/-- Disabled — proves `g⁻¹ * n * g ∈ N` directly. -/
TheoremDoc Subgroup.Normal.conj_mem' as "conj_mem'" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem MonoidHom.normal_ker Subgroup.Normal.conj_mem Subgroup.Normal.conj_mem'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b g : G)
    (ha : a ∈ f.ker) (hb : b ∈ f.ker) : g * (a * b) * g⁻¹ ∈ f.ker := by
  Hint "First, combine `a` and `b` into a single kernel element.
  Since `f.ker` is a subgroup, it's closed under multiplication:
  `have hab := f.ker.mul_mem {ha} {hb}`."
  Branch
    rw [MonoidHom.mem_ker] at ha hb ⊢
    rw [map_mul, map_mul, map_mul, map_inv, ha, hb]
    rw [mul_one, mul_one, mul_inv_cancel]
  have hab := f.ker.mul_mem ha hb
  Hint "Now `{hab} : a * b ∈ f.ker`. The rest is the same conjugation
  proof as Level 5 — unfold and push `f` through.

  `rw [MonoidHom.mem_ker] at {hab} ⊢`."
  rw [MonoidHom.mem_ker] at hab ⊢
  Hint "Push `f` through: `rw [map_mul, map_mul, map_inv]`."
  rw [map_mul, map_mul, map_inv]
  Hint "Substitute `{hab} : f (a * b) = 1`: `rw [{hab}]`."
  rw [hab]
  Hint (hidden := true) "`rw [mul_one]` then `exact mul_inv_cancel (f g)`."
  rw [mul_one]
  exact mul_inv_cancel (f g)

Conclusion
"
Using `have` to combine kernel elements first made the proof cleaner —
instead of pushing `f` through four factors, you reduced to the
one-element conjugation from Level 6.

This is the **strategic use of `have`**: simplify the problem before
attacking it. On paper: *Since `a, b ∈ ker(f)`, we have `ab ∈ ker(f)`.
Then `f(g · ab · g⁻¹) = f(g) · f(ab) · f(g)⁻¹ = f(g) · 1 · f(g)⁻¹ = 1`,
so `g(ab)g⁻¹ ∈ ker(f)`.*

You now have all the pieces for the boss: the Normal constructor shape
(Level 2), the `have` tactic (Level 3), and the kernel conjugation
algebra (Level 6). Time to put them together.
"
