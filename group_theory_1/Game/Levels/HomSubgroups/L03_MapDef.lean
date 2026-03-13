import Game.Metadata

World "HomSubgroups"
Level 3

Title "Image of a Subgroup"

Introduction
"
If `K` is a subgroup of `G` and `f : G →* H`, the **image**
`f(K) = {f(x) | x ∈ K}` is a subgroup of `H`.

Lean calls this `Subgroup.map f K`.

The unfolding lemma is:

`Subgroup.mem_map : y ∈ K.map f ↔ ∃ x ∈ K, f x = y`

Unlike `mem_comap` (a property check: does `f x ∈ K`?), `mem_map`
requires producing a **witness** — an element of `K` that maps to `y`.
This is the image-reasoning move from Kernel and Image, now applied
to a specific subgroup.

Prove that `f a` is in the image when `a ∈ K`.
"

/-- The image of a subgroup `K` under a group homomorphism `f`.

`Subgroup.map f K` is the subgroup `{y ∈ H | ∃ x ∈ K, f x = y}`.

Use `rw [Subgroup.mem_map]` to convert between `y ∈ K.map f` and
`∃ x ∈ K, f x = y`. -/
DefinitionDoc Subgroup.map as "Subgroup.map"

NewDefinition Subgroup.map

/-- `Subgroup.mem_map` says: for a group homomorphism `f : G →* H`
and a subgroup `K` of `G`,

`y ∈ K.map f ↔ ∃ x ∈ K, f x = y`

Use `rw [Subgroup.mem_map]` to unfold image membership, then
provide a witness with `exact ⟨w, hw, proof⟩`. -/
TheoremDoc Subgroup.mem_map as "Subgroup.mem_map" in "Hom"

NewTheorem Subgroup.mem_map

/-- Disabled — prove image membership from `mem_map` instead. -/
TheoremDoc Subgroup.mem_map_of_mem as "Subgroup.mem_map_of_mem" in "Hom"

/-- Disabled — prove image membership from `mem_map` instead. -/
TheoremDoc Subgroup.apply_coe_mem_map as "Subgroup.apply_coe_mem_map" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem Subgroup.mem_map_of_mem Subgroup.apply_coe_mem_map

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (a : G) (ha : a ∈ K) :
    f a ∈ K.map f := by
  Hint "Unfold image membership: `rw [Subgroup.mem_map]`."
  rw [Subgroup.mem_map]
  Hint "The goal is `∃ x ∈ K, f x = f a`. You need a witness — an
  element of `K` that maps to `f a`. The obvious choice is `a` itself.

  Provide the full witness: `exact ⟨a, {ha}, rfl⟩`."
  Branch
    -- Alternative: use tactic for witness (closes all remaining goals)
    Hint (hidden := true) "You can also provide the witness with `use a`.
    It fills in `a ∈ K` and `f a = f a` automatically."
    use a
  exact ⟨a, ha, rfl⟩

Conclusion
"
To prove `y ∈ map f K`, you must produce a witness: some `x ∈ K` with
`f x = y`.

Contrast preimage and image membership:

| Operation | Membership | Proof obligation |
|-----------|-----------|------------------|
| `comap f K` | `x ∈ K.comap f ↔ f x ∈ K` | Property check |
| `map f K` | `y ∈ K.map f ↔ ∃ x ∈ K, f x = y` | Witness production |

The preimage is easier to work with — you just check a property.
The image requires constructing an explicit preimage element.

You already know two special cases:
- `f.ker = comap f ⊥` — the preimage of the trivial subgroup
- `f.range = map f ⊤` — the image of the whole group

You'll prove the first of these in Level 5.
"
