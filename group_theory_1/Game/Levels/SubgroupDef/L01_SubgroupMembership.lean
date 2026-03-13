import Game.Metadata

World "SubgroupDef"
Level 1

Title "What Is a Subgroup?"

Introduction
"
A **subgroup** of a group `G` is a subset `H ⊆ G` that is itself a
group under the same operation. In Lean, this is captured by the type
`Subgroup G`.

If `H : Subgroup G` and `x : G`, we write `x ∈ H` to say that `x`
belongs to the subgroup `H`. This uses the same `∈` notation you know
from sets.

Every subgroup contains the identity element `1`. This is the theorem
`one_mem`:

`one_mem H : 1 ∈ H`

Prove that `1` belongs to `H`.
"

/-- A `Subgroup G` is a subset of a group `G` that contains `1`,
is closed under multiplication, and is closed under inverses.

If `H : Subgroup G`, you can write `x ∈ H` to test membership.

The three key properties are:
- `one_mem H : 1 ∈ H`
- `mul_mem : x ∈ H → y ∈ H → x * y ∈ H`
- `inv_mem : x ∈ H → x⁻¹ ∈ H` -/
DefinitionDoc Subgroup as "Subgroup"

/-- `one_mem H` says that `1 ∈ H` — every subgroup contains the
identity element.

This requires no hypotheses: if `H` is a subgroup, then `1 ∈ H`
automatically.

Use it with `exact one_mem H` when the goal is `1 ∈ H`. -/
TheoremDoc OneMemClass.one_mem as "one_mem" in "Subgroup"

NewDefinition Subgroup
NewTheorem OneMemClass.one_mem

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) : (1 : G) ∈ H := by
  Hint "The goal is `1 ∈ H`. The theorem `one_mem` says exactly this
  for any subgroup `H`. Try `exact one_mem H`."
  exact one_mem H

Conclusion
"
Every subgroup contains `1`. This is the first of three closure
properties that define what it means to be a subgroup:

1. **Identity**: `1 ∈ H` (`one_mem`)
2. **Multiplication**: if `x ∈ H` and `y ∈ H`, then `x * y ∈ H`
3. **Inverses**: if `x ∈ H`, then `x⁻¹ ∈ H`

In the next two levels, you'll see the other two properties.
"
