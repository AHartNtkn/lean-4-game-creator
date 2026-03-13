import Game.Metadata

World "HomSubgroups"
Level 7

Title "Boss — The Galois Connection"

Introduction
"
The fundamental relationship between `map` and `comap`:

`map f K ≤ L  ↔  K ≤ comap f L`

This says: pushing `K` forward lands inside `L` if and only if `K`
is already inside the preimage of `L`.

The forward direction is the easier one: it reduces image reasoning
(witness production) to preimage reasoning (property checking). The
backward direction requires extracting a witness from `mem_map` and
unfolding `mem_comap`.

Start with `refine ⟨?_, ?_⟩` to split the `↔`.
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Subgroup.map_le_iff_le_comap as "Subgroup.map_le_iff_le_comap" in "Hom"

/-- Disabled — this follows from the Galois connection. -/
TheoremDoc Subgroup.le_comap_map as "Subgroup.le_comap_map" in "Hom"

/-- Disabled — you proved this in Level 6. -/
TheoremDoc Subgroup.map_comap_le as "Subgroup.map_comap_le" in "Hom"

/-- Disabled — blocks Galois connection exploit. -/
TheoremDoc Subgroup.gc_map_comap as "Subgroup.gc_map_comap" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem Subgroup.map_le_iff_le_comap Subgroup.map_comap_le Subgroup.le_comap_map Subgroup.gc_map_comap

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (L : Subgroup H) :
    K.map f ≤ L ↔ K ≤ L.comap f := by
  Hint "Split the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · -- Forward: map f K ≤ L → K ≤ comap f L
    Hint "Introduce the hypothesis and an element:
    `intro h x hx`.

    You need to show `x ∈ L.comap f`, i.e., `f x ∈ L`."
    intro h x hx
    Hint "Unfold preimage membership: `rw [Subgroup.mem_comap]`."
    rw [Subgroup.mem_comap]
    Hint "The goal is `f x ∈ L`. Since `{h} : K.map f ≤ L`, it
    suffices to show `f x ∈ K.map f`.

    Use `apply {h}` to reduce the goal."
    apply h
    Hint "The goal is `f x ∈ K.map f`. Unfold image membership:
    `rw [Subgroup.mem_map]`."
    rw [Subgroup.mem_map]
    Hint (hidden := true) "Provide the witness: `exact ⟨x, {hx}, rfl⟩`."
    exact ⟨x, hx, rfl⟩
  · -- Backward: K ≤ comap f L → map f K ≤ L
    Hint "Introduce the hypothesis and an element:
    `intro h y hy`."
    intro h y hy
    Hint "Unfold image membership: `rw [Subgroup.mem_map] at {hy}`."
    rw [Subgroup.mem_map] at hy
    Hint "Extract the witness: `obtain ⟨x, hxK, hfx⟩ := {hy}`."
    obtain ⟨x, hxK, hfx⟩ := hy
    Hint "You have `hxK : x ∈ K` and `hfx : f x = y`. Apply the
    containment hypothesis: since `x ∈ K` and `{h} : K ≤ L.comap f`,
    we get `x ∈ L.comap f`.

    `have hxL := {h} hxK`."
    have hxL := h hxK
    Hint "Now `hxL : x ∈ L.comap f`. Unfold preimage membership:
    `rw [Subgroup.mem_comap] at hxL`."
    rw [Subgroup.mem_comap] at hxL
    Hint "Now `hxL : f x ∈ L` and `hfx : f x = y`. Substitute:
    `rw [← hfx]`."
    rw [← hfx]
    Hint (hidden := true) "`exact hxL`."
    exact hxL

Conclusion
"
Congratulations on completing **Homomorphism Subgroups**!

You proved the **Galois connection** between `map` and `comap`:

> **`map f K ≤ L  ↔  K ≤ comap f L`**

This says that `map f` and `comap f` are adjoint operations: pushing
forward and pulling back are interchangeable when asking about
containment.

On paper: *Let `f : G → H` be a homomorphism, `K ≤ G`, `L ≤ H`.
Then `f(K) ⊆ L` iff `K ⊆ f⁻¹(L)`. Forward: if `f(K) ⊆ L`, then
for any `x ∈ K`, `f(x) ∈ f(K) ⊆ L`, so `x ∈ f⁻¹(L)`. Backward:
if `K ⊆ f⁻¹(L)`, take `y ∈ f(K)`, write `y = f(x)` for some
`x ∈ K ⊆ f⁻¹(L)`, so `f(x) ∈ L`, i.e., `y ∈ L`.*

Notice the **comap/map asymmetry**: the forward direction is easier
because it reduces the hard operation (image: produce a witness) to
the easy one (preimage: check a property). This is the core benefit
of the adjunction — it translates image questions into preimage
questions.

The Galois connection implies both unit laws:
- `K ≤ comap f (map f K)` (take `L = map f K`, forward direction)
- `map f (comap f L) ≤ L` (Level 6, take `K = comap f L`, backward)

Summary of `comap` and `map`:

| Operation | Membership | Direction | Special case |
|-----------|-----------|-----------|--------------|
| `comap f K` | `f x ∈ K` | Pull back (target → source) | `comap f ⊥ = ker f` |
| `map f K` | `∃ x ∈ K, f x = y` | Push forward (source → target) | `map f ⊤ = range f` |

Proof moves learned:
- **Hom-through-comap**: unfold `mem_comap`, apply hom property, close with subgroup closure
- **Image witness selection**: unfold `mem_map`, provide `⟨x, hx, rfl⟩`
- **Galois adjunction**: `map f K ≤ L ↔ K ≤ comap f L`

Looking ahead: you'll next study cosets and normal subgroups. The
preimage operation returns when you prove that the preimage of a
normal subgroup is normal — a key step toward quotient groups.
"
