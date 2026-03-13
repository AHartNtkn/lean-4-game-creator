import Game.Metadata

World "SubgroupBasics"
Level 1

Title "Subgroup Containment"

Introduction
"
If `H` and `K` are both subgroups of `G`, we write `H ≤ K` to mean
that every element of `H` is also an element of `K`. This is the
subgroup analogue of `⊆` for sets.

In Lean, `H ≤ K` is *defined* as `∀ ⦃x⦄, x ∈ H → x ∈ K`. So if you
have `hle : H ≤ K` and `ha : a ∈ H`, you can apply `hle` to `ha`
to get `a ∈ K` — just like a function.

Prove that if `H ≤ K` and `a ∈ H`, then `a ∈ K`.
"

/-- If `H ≤ K` for subgroups `H K : Subgroup G`, then every element
of `H` is also in `K`.

`H ≤ K` is defined as `∀ ⦃x⦄, x ∈ H → x ∈ K`, so `hle : H ≤ K`
acts like a function: given `ha : a ∈ H`, `hle ha : a ∈ K`.

The symbol `≤` is typed `\le`. -/
DefinitionDoc Subgroup.instLE as "Subgroup.LE (≤)"

NewDefinition Subgroup.instLE

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (a : G) (ha : a ∈ H) : a ∈ K := by
  Hint "You have `hle : H ≤ K` and `ha : a ∈ H`. Since `H ≤ K`
  means `∀ x, x ∈ H → x ∈ K`, the hypothesis `hle` works like a
  function: `exact hle ha`."
  exact hle ha

Conclusion
"
`H ≤ K` is the ordering relation on subgroups, and it works just
like function application: `hle ha` converts membership in `H` to
membership in `K`.

You'll use this constantly when working with the subgroup lattice.
For example, if you know `H ≤ K` and want to show `a * b ∈ K`, you
can first show `a * b ∈ H` (perhaps using `mul_mem`) and then apply
`hle`.

The subgroup ordering has two extremes: a smallest subgroup `⊥` and
a largest subgroup `⊤`. You'll meet them in the next levels.
"
