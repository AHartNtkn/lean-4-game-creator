import Game.Metadata

World "SubgroupBasics"
Level 5

Title "Intersection Membership"

Introduction
"
Given two subgroups `H` and `K` of `G`, their **intersection**
`H ⊓ K` (typed `\\inf` or `\\sqcap`) is the subgroup whose elements
belong to *both* `H` and `K`.

The key lemma is `Subgroup.mem_inf`:

`Subgroup.mem_inf : x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K`

The right-hand side uses `∧` (\"and\"). If `h : P ∧ Q`, then
`h.1 : P` and `h.2 : Q` extract the two parts.

Given `a ∈ H ⊓ K`, prove that `a ∈ H`.
"

/-- `Subgroup.mem_inf` characterizes membership in the intersection
of two subgroups:

`Subgroup.mem_inf : x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K`

To use it forward: `Subgroup.mem_inf.mp ha` converts
`ha : a ∈ H ⊓ K` into `a ∈ H ∧ a ∈ K`.

To rewrite: `rw [Subgroup.mem_inf] at ha` changes `ha` in place.

Once you have `h : P ∧ Q`, use `h.1` for `P` and `h.2` for `Q`.

The symbol `⊓` is typed `\\inf` or `\\sqcap`. -/
TheoremDoc Subgroup.mem_inf as "Subgroup.mem_inf" in "Subgroup"

NewTheorem Subgroup.mem_inf

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G)
    (a : G) (ha : a ∈ H ⊓ K) : a ∈ H := by
  Hint "You have `ha : a ∈ H ⊓ K` and need `a ∈ H`. First, convert
  the intersection membership using `rw [Subgroup.mem_inf] at ha`.
  This changes `ha` to `a ∈ H ∧ a ∈ K`. Then extract the first
  component with `exact ha.1`."
  rw [Subgroup.mem_inf] at ha
  Hint "Now `ha : a ∈ H ∧ a ∈ K`. The `.1` projection gives the
  left half: `exact ha.1`."
  exact ha.1

Conclusion
"
The `rw [Subgroup.mem_inf] at ha` step converts intersection
membership into a conjunction (`∧`), and `.1` extracts the left half.

You've seen how to *take apart* a conjunction with `.1` and `.2`.
In the next level, you'll learn how to *build* one.
"
