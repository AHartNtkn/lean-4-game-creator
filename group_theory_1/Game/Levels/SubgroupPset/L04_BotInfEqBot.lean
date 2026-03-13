import Game.Metadata

World "SubgroupPset"
Level 4

Title "Intersecting with the Trivial Subgroup"

Introduction
"
If one of the subgroups in an intersection is trivial, the
intersection is trivial. Prove `⊥ ⊓ H = ⊥`.

The forward direction is straightforward. The backward direction
has a twist: you'll need to show an element of `⊥` is also in `H`.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) : ⊥ ⊓ H = ⊥ := by
  Hint "Use `ext x` to reduce to membership, then split the `↔`
  with `refine ⟨?_, ?_⟩`."
  ext x
  refine ⟨?_, ?_⟩
  · Hint "**Forward**: `x ∈ ⊥ ⊓ H → x ∈ ⊥`. Extract the
    `⊥`-component from the intersection."
    intro hx
    rw [Subgroup.mem_inf] at hx
    Hint (hidden := true) "`exact hx.1` or
    `obtain ⟨hbot, _⟩ := hx; exact hbot`."
    exact hx.1
  · Hint "**Backward**: `x ∈ ⊥ → x ∈ ⊥ ⊓ H`. If `x ∈ ⊥`,
    then `x = 1`. Once you know that, can you show `1 ∈ H`?"
    intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    rw [Subgroup.mem_inf]
    Hint (hidden := true) "`rw [Subgroup.mem_bot]; exact ⟨rfl, one_mem H⟩`"
    rw [Subgroup.mem_bot]
    exact ⟨rfl, one_mem H⟩

Conclusion
"
The forward direction was routine extraction. The backward direction
was the twist: knowing `x ∈ ⊥` means `x = 1` (via `Subgroup.mem_bot`),
then rewriting with this identity reduces everything to facts about `1`.

This **reduce-to-identity** pattern — use `mem_bot` to learn `x = 1`,
rewrite, then verify using `one_mem` — will recur whenever you reason
about the trivial subgroup. You'll see it again when proving that an
injective homomorphism has trivial kernel.

On paper: *Forward: if `x ∈ ⊥ ∩ H`, then `x ∈ ⊥`. Backward: if
`x ∈ ⊥`, then `x = 1`, so `x ∈ H` (since `1 ∈ H`) and `x ∈ ⊥`
(given), hence `x ∈ ⊥ ∩ H`.*
"
