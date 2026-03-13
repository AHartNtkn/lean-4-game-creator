import Game.Metadata

World "HomBasics"
Level 5

Title "Range Closed Under Inverses"

Introduction
"
The range, like the kernel, is a subgroup. To see this concretely:
if `y ∈ f.range`, then `y⁻¹ ∈ f.range` too.

The idea: if `y = f(x)` for some `x`, then `y⁻¹ = f(x)⁻¹ = f(x⁻¹)`,
so `x⁻¹` is a witness for `y⁻¹`.

The proof pattern:
1. Unfold `hy`: `rw [MonoidHom.mem_range] at hy`
2. Extract the witness: `obtain ⟨x, hx⟩ := hy`
3. Unfold the goal: `rw [MonoidHom.mem_range]`
4. Provide the new witness: `use x⁻¹`
5. Verify: `rw [map_inv, hx]`
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem InvMemClass.inv_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (y : H)
    (hy : y ∈ f.range) : y⁻¹ ∈ f.range := by
  Hint "Unfold the range hypothesis: `rw [MonoidHom.mem_range] at {hy}`."
  rw [MonoidHom.mem_range] at hy
  Hint "Now `{hy} : ∃ x, f x = y`. Extract the witness:
  `obtain ⟨x, hx⟩ := {hy}`."
  obtain ⟨x, hx⟩ := hy
  Hint "You have `hx : f x = y`. Now unfold the goal:
  `rw [MonoidHom.mem_range]`."
  rw [MonoidHom.mem_range]
  Hint "The goal is `∃ x_1, f x_1 = y⁻¹`. What element of `G` maps to
  `y⁻¹`? Since `f(x) = y`, we have `f(x⁻¹) = f(x)⁻¹ = y⁻¹`.

  Provide the witness: `use x⁻¹`."
  use x⁻¹
  Hint "The goal is `f x⁻¹ = y⁻¹`. Push `f` through the inverse:
  `rw [map_inv]`."
  rw [map_inv]
  Hint (hidden := true) "The goal is `(f x)⁻¹ = y⁻¹`. Substitute
  `hx : f x = y`: `rw [hx]`."
  rw [hx]

Conclusion
"
The full **image-reasoning move**:

1. `obtain ⟨x, hx⟩ := hy` — extract the witness from `∃`
2. `use x⁻¹` — propose the new witness
3. `rw [map_inv, hx]` — verify it works

This `obtain` → `use` → verify pattern works for any range closure
proof. The range is closed under `*`, `⁻¹`, and contains `1` —
it is a `Subgroup H`, just like the kernel is a `Subgroup G`.

Contrast the two reasoning patterns:

| Move | Shape | Tool |
|------|-------|------|
| **Kernel reasoning** | Unfold `mem_ker`, prove `f x = 1` | `rw` + algebra |
| **Image reasoning** | Unfold `mem_range`, find witness | `obtain` + `use` + verify |
"
