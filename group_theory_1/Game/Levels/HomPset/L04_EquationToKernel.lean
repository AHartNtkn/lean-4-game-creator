import Game.Metadata

World "HomPset"
Level 4

Title "From Equation to Kernel"

Introduction
"
The Homomorphisms boss went from `f(a) = f(b)` to `f(a * b⁻¹) = 1`.
Here's the reverse direction in a different form.

Given an equation `f(a) * f(b) = f(c)` in the target group,
conclude that `a * b * c⁻¹` lands in the kernel.

The idea: push `f` through `a * b * c⁻¹` to get
`f(a) * f(b) * f(c)⁻¹`, then substitute the hypothesis and cancel.
"

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b c : G)
    (h : f a * f b = f c) : a * b * c⁻¹ ∈ f.ker := by
  Hint "Unfold kernel membership: `rw [MonoidHom.mem_ker]`."
  rw [MonoidHom.mem_ker]
  Hint "Push `f` through `a * b * c⁻¹`:
  `rw [map_mul, map_mul, map_inv]`."
  rw [map_mul, map_mul, map_inv]
  Hint "The goal is `f a * f b * (f c)⁻¹ = 1`. Substitute `{h}`:
  `rw [{h}]`."
  rw [h]
  Hint (hidden := true) "The goal is `f c * (f c)⁻¹ = 1`. Use
  `exact mul_inv_cancel (f c)`."
  exact mul_inv_cancel (f c)

Conclusion
"
Given any equation `f(a) · f(b) = f(c)` in the target, you
proved `a · b · c⁻¹ ∈ ker(f)`.

This is the kernel's role as a measuring device: it captures the
\"difference\" between elements that `f` sends to the same place.
More precisely, `f(x) = f(y)` if and only if `x · y⁻¹ ∈ ker(f)`.

The proof pattern is the reverse of the Homomorphisms boss:
there you started with `f(a) = f(b)` and derived `f(ab⁻¹) = 1`;
here you started with `f(a) · f(b) = f(c)` and derived
`a · b · c⁻¹ ∈ ker(f)`.

This is the **kernel calculation**: unfold membership, push `f`
through, substitute the kernel equation, cancel. You've now used
this pattern in three levels — recognizing it as a single move
will serve you well later, especially when proving kernels are
normal subgroups.

On paper: *`f(abc⁻¹) = f(a)f(b)f(c)⁻¹ = f(c)f(c)⁻¹ = 1`,
so `abc⁻¹ ∈ ker(f)`.*
"
