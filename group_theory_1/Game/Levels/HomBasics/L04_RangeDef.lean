import Game.Metadata

World "HomBasics"
Level 4

Title "The Range of a Homomorphism"

Introduction
"
The kernel captures what `f` destroys. The **range** captures what
`f` reaches.

`f.range = {y ∈ H | ∃ x : G, f(x) = y}`

In Lean, `f.range` is a `Subgroup H`. The unfolding lemma is:

`MonoidHom.mem_range : y ∈ f.range ↔ ∃ x, f x = y`

Unlike kernel membership (which is a *property check*: does `f x = 1`?),
range membership requires producing a **witness** — an element of `G`
that maps to the target.

Prove that `f a` is in the range by providing the witness `a`.
"

/-- The range (image) of a group homomorphism `f : G →* H`.

`f.range` is the subgroup `{y ∈ H | ∃ x : G, f x = y}`.

This is the set of elements in `H` that `f` actually reaches. -/
DefinitionDoc MonoidHom.range as "MonoidHom.range"

NewDefinition MonoidHom.range

/-- `MonoidHom.mem_range` says: for a group homomorphism `f : G →* H`,

`y ∈ f.range ↔ ∃ x, f x = y`

Use `rw [MonoidHom.mem_range]` to unfold range membership into
an existential statement, then provide a witness with `exact ⟨w, proof⟩`. -/
TheoremDoc MonoidHom.mem_range as "MonoidHom.mem_range" in "Hom"

NewTheorem MonoidHom.mem_range

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a : G) :
    f a ∈ f.range := by
  Hint "Use `rw [MonoidHom.mem_range]` to unfold range membership."
  rw [MonoidHom.mem_range]
  Hint "The goal is `∃ x, f x = f a`. You need to provide a witness —
  an element of `G` that maps to `f a`. The obvious choice is `a` itself.

  Use `use a` to provide the witness."
  Branch
    exact ⟨a, rfl⟩
  use a

Conclusion
"
The range of `f` is the set of elements that `f` actually hits.
To prove `y ∈ f.range`, you must produce a **witness**: an element
`x` with `f x = y`.

Contrast the two subgroups:

| | Kernel | Range |
|--|--------|-------|
| **Lives in** | `G` (source) | `H` (target) |
| **Membership** | `f x = 1` (property) | `∃ x, f x = y` (witness) |
| **Measures** | Information destroyed | Information reached |

Kernel reasoning asks: *does this element map to 1?*
Image reasoning asks: *can I find a preimage?*

The **image-reasoning move**: unfold `mem_range`, produce a witness
`⟨x, proof⟩`.
"
