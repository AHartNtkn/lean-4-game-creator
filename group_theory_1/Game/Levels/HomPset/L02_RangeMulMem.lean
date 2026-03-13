import Game.Metadata

World "HomPset"
Level 2

Title "Range Closed Under Multiplication"

Introduction
"
In Kernel and Image you showed the range is closed under inverses.
Now show it's closed under multiplication.

If `y₁ = f(x₁)` and `y₂ = f(x₂)`, then `y₁ * y₂ = f(x₁) * f(x₂) = f(x₁ * x₂)`.
So `x₁ * x₂` is a witness for `y₁ * y₂`.

The pattern:
1. Unfold both range hypotheses with `rw [MonoidHom.mem_range] at h₁ h₂`
2. Extract witnesses: `obtain ⟨x₁, hx₁⟩ := h₁` and `obtain ⟨x₂, hx₂⟩ := h₂`
3. Unfold the goal: `rw [MonoidHom.mem_range]`
4. Provide the combined witness: `use x₁ * x₂`
5. Verify: `rw [map_mul, hx₁, hx₂]`
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MulMemClass.mul_mem Subgroup.mul_mem Submonoid.mul_mem SubgroupClass.mul_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (y₁ y₂ : H)
    (h₁ : y₁ ∈ f.range) (h₂ : y₂ ∈ f.range) : y₁ * y₂ ∈ f.range := by
  Hint "Unfold both range hypotheses:
  `rw [MonoidHom.mem_range] at {h₁} {h₂}`."
  rw [MonoidHom.mem_range] at h₁ h₂
  Hint "Extract the witnesses: `obtain ⟨x₁, hx₁⟩ := {h₁}` and then
  `obtain ⟨x₂, hx₂⟩ := {h₂}`."
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  Hint "Unfold the goal: `rw [MonoidHom.mem_range]`."
  rw [MonoidHom.mem_range]
  Hint "Since `{hx₁} : f x₁ = y₁` and `{hx₂} : f x₂ = y₂`, the
  element `x₁ * x₂` witnesses `y₁ * y₂ ∈ f.range`.

  Provide it: `use x₁ * x₂`."
  use x₁ * x₂
  Hint (hidden := true) "Verify with `rw [map_mul, {hx₁}, {hx₂}]`."
  rw [map_mul, hx₁, hx₂]

Conclusion
"
The **image-reasoning move** from Kernel and Image, now with two witnesses:

1. **Obtain** witnesses from the hypotheses
2. **Combine** them using the group operation
3. **Use** the combined element as the new witness
4. **Verify** with `map_mul` (or `map_inv`, `map_one`)

This is the same pattern you used for range closure under inverses
in Kernel and Image — `obtain` then `use` then verify. The difference
is only in step 2: here you multiply the witnesses, there you inverted.

You've now shown that `range(f)` is closed under multiplication
(this level) and under inverses (Kernel and Image L5). Closure
under the identity — `1 ∈ range(f)` — is a two-liner: `use 1`
then `exact map_one f`.

On paper: *If `y₁ = f(x₁)` and `y₂ = f(x₂)`, then
`y₁y₂ = f(x₁)f(x₂) = f(x₁x₂)`, so `y₁y₂ ∈ range(f)`.*
"
