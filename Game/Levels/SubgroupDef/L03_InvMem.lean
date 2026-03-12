import Game.Metadata

World "SubgroupDef"
Level 3

Title "Closure Under Inverses"

Introduction
"
The third closure property: if `x ∈ H`, then `x⁻¹ ∈ H`.

The theorem `inv_mem` captures this:

`inv_mem : x ∈ H → x⁻¹ ∈ H`

Prove that `a⁻¹ ∈ H`.
"

/-- `inv_mem` says that if `x ∈ H`, then `x⁻¹ ∈ H` — subgroups
are closed under inverses.

Use it with `exact inv_mem hx` where `hx : x ∈ H`. -/
TheoremDoc InvMemClass.inv_mem as "inv_mem" in "Subgroup"

NewTheorem InvMemClass.inv_mem

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) (a : G)
    (ha : a ∈ H) : a⁻¹ ∈ H := by
  Hint "The goal is `a⁻¹ ∈ H`. You have `ha : a ∈ H`.

  Try `exact inv_mem ha`."
  exact inv_mem ha

Conclusion
"
You now know all three closure properties of a subgroup:

| Theorem | Statement |
|---------|-----------|
| `one_mem H` | `1 ∈ H` |
| `mul_mem` | `x ∈ H → y ∈ H → x * y ∈ H` |
| `inv_mem` | `x ∈ H → x⁻¹ ∈ H` |

These are the three things you need to *use* a subgroup. But they
are also the three things you need to *build* one — which is where
this world is headed.

First, let's combine these tools in a slightly harder problem.
"
