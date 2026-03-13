import Game.Metadata

World "HomSubgroups"
Level 2

Title "Preimage Closed Under Multiplication"

Introduction
"
If `f(a) ∈ K` and `f(b) ∈ K`, is `f(a * b) ∈ K`?

Since `f(a * b) = f(a) · f(b)` and `K` is closed under multiplication,
yes: `f(a) · f(b) ∈ K`.

The proof follows the same hom-through-comap pattern from Level 1.
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MulMemClass.mul_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (K : Subgroup H) (a b : G)
    (ha : a ∈ K.comap f) (hb : b ∈ K.comap f) :
    a * b ∈ K.comap f := by
  Hint "Unfold `mem_comap` at the hypotheses and the goal:
  `rw [Subgroup.mem_comap] at {ha} {hb} ⊢`."
  rw [Subgroup.mem_comap] at ha hb ⊢
  Hint "The goal is `f (a * b) ∈ K`. Push `f` through the product:
  `rw [map_mul]`."
  rw [map_mul]
  Hint (hidden := true) "The goal is `f a * f b ∈ K`. Use
  `exact K.mul_mem {ha} {hb}`."
  exact K.mul_mem ha hb

Conclusion
"
The pattern is always the same: unfold `mem_comap`, push `f` through
the expression, close with subgroup closure. The `inv_mem` case is
identical (using `map_inv` and `K.inv_mem`).

The key insight: **the preimage of a subgroup is automatically a
subgroup**, because the hom property converts group operations in `G`
to group operations in `H`, and subgroup closure in `H` pulls back.

On paper: *Since `f(a) ∈ K` and `f(b) ∈ K`, we have
`f(a · b) = f(a) · f(b) ∈ K`, so `a · b ∈ f⁻¹(K)`.*
"
