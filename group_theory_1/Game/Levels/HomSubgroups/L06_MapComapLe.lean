import Game.Metadata

World "HomSubgroups"
Level 6

Title "Image of Preimage is Contained"

Introduction
"
If you take a subgroup `L` of `H`, pull it back to `G` via `comap f`,
then push the result forward via `map f`, do you get `L` back?

Not necessarily — you might lose elements that aren't in the range of
`f`. But you always get a subset: `map f (comap f L) ≤ L`.

The proof uses `obtain` to extract the witness from `mem_map`, then
`mem_comap` to read off membership in `L`.
"

/-- Disabled — you are proving a related result yourself. -/
TheoremDoc Subgroup.map_comap_le as "Subgroup.map_comap_le" in "Hom"

/-- Disabled — you are proving this in the boss level. -/
TheoremDoc Subgroup.map_le_iff_le_comap as "Subgroup.map_le_iff_le_comap" in "Hom"

TheoremTab "Hom"

/-- Disabled — blocks Galois connection exploit. -/
TheoremDoc Subgroup.gc_map_comap as "Subgroup.gc_map_comap" in "Hom"

DisabledTactic simp group
DisabledTheorem Subgroup.map_comap_le Subgroup.map_le_iff_le_comap Subgroup.gc_map_comap

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (L : Subgroup H) :
    Subgroup.map f (Subgroup.comap f L) ≤ L := by
  Hint "Unfold `≤` by introducing an element and its membership proof:
  `intro y hy`."
  intro y hy
  Hint "You have `{hy} : y ∈ (Subgroup.comap f L).map f`. Unfold image
  membership: `rw [Subgroup.mem_map] at {hy}`."
  rw [Subgroup.mem_map] at hy
  Hint "Now `{hy} : ∃ x ∈ Subgroup.comap f L, f x = y`. Extract the
  witness: `obtain ⟨x, hx, hfx⟩ := {hy}`."
  obtain ⟨x, hx, hfx⟩ := hy
  Hint "You have `hx : x ∈ Subgroup.comap f L` and `hfx : f x = y`.
  Unfold preimage membership: `rw [Subgroup.mem_comap] at hx`."
  rw [Subgroup.mem_comap] at hx
  Hint "Now `hx : f x ∈ L` and `hfx : f x = y`. The goal is `y ∈ L`.
  Substitute: `rw [← hfx]`."
  rw [← hfx]
  Hint (hidden := true) "`exact hx`."
  exact hx

Conclusion
"
The round trip `L ↦ comap f L ↦ map f (comap f L)` always gives a
subset of `L`. The argument:

1. Take `y ∈ map f (comap f L)`
2. Extract witness: `x ∈ comap f L` with `f x = y`
3. Unfold: `f x ∈ L`
4. Substitute: `y = f x ∈ L`

The reverse containment `L ≤ map f (comap f L)` fails in general —
elements of `L` that aren't in the range of `f` can't be pulled back
and pushed forward.

In the boss, you'll prove the general relationship between `map` and
`comap`: the **Galois connection** `map f K ≤ L ↔ K ≤ comap f L`.
This level's argument is essentially the backward direction of that
equivalence, applied to the specific case `K = comap f L`.
"
