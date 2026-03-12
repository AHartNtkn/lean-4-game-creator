import Game.Metadata

World "SubgroupDef"
Level 2

Title "Closure Under Multiplication"

Introduction
"
A subgroup is closed under multiplication: if `x` and `y` both
belong to `H`, then so does their product `x * y`.

The theorem `mul_mem` captures this:

`mul_mem : x ∈ H → y ∈ H → x * y ∈ H`

Given proofs that `x ∈ H` and `y ∈ H`, you can write
`exact mul_mem hx hy` to conclude `x * y ∈ H`.

Prove that `a * b ∈ H`.
"

/-- `mul_mem` says that if `x ∈ H` and `y ∈ H`, then `x * y ∈ H` —
subgroups are closed under multiplication.

Use it with `exact mul_mem hx hy` where `hx : x ∈ H` and
`hy : y ∈ H`, or with `apply mul_mem` to split the goal into
two membership goals. -/
TheoremDoc MulMemClass.mul_mem as "mul_mem" in "Subgroup"

NewTheorem MulMemClass.mul_mem

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  Hint "The goal is `a * b ∈ H`. You have `ha : a ∈ H` and
  `hb : b ∈ H`. The theorem `mul_mem` combines these.

  Try `exact mul_mem ha hb`."
  Branch
    apply mul_mem
    · exact ha
    · exact hb
  exact mul_mem ha hb

Conclusion
"
Subgroups are closed under multiplication. Combined with `one_mem`,
you can already prove that any *product* of elements from `H` stays
in `H`. For instance, `a * b * c ∈ H` follows from applying
`mul_mem` twice.

One more closure property to go: inverses.
"
