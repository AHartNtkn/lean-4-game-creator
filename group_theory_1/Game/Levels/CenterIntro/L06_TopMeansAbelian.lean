import Game.Metadata

World "CenterIntro"
Level 6

Title "Full Center Means Abelian"

Introduction
"
Now the converse: if `center G = ⊤` (every element is in the center),
then the group is abelian — every pair of elements commutes.

The proof extracts commutativity from the hypothesis in three steps:
1. `rw [Subgroup.eq_top_iff'] at h` to convert `center G = ⊤` to `∀ z, z ∈ center G`
2. `apply Subgroup.mem_center_iff.mp` to reduce the goal to a center membership
3. `exact h y` to close the membership goal
"

TheoremTab "Center"

DisabledTactic group

Statement (G : Type*) [Group G] (h : Subgroup.center G = ⊤)
    (x y : G) : x * y = y * x := by
  Hint "Start by converting `h` from `center G = ⊤` to `∀ z, z ∈ center G`:

  `rw [Subgroup.eq_top_iff'] at h`"
  rw [Subgroup.eq_top_iff'] at h
  Hint "Now `h : ∀ (x : G), x ∈ Subgroup.center G`.

  The goal is `{x} * {y} = {y} * {x}`. This looks like the commuting
  condition from `mem_center_iff` applied to `{y}` and `{x}`.

  Use `apply Subgroup.mem_center_iff.mp` — this changes the goal to
  `{y} ∈ Subgroup.center G` (Lean figures out which element to use)."
  Branch
    exact Subgroup.mem_center_iff.mp (h y) x
  Branch
    have hy := h y
    rw [Subgroup.mem_center_iff] at hy
    exact hy x
  apply Subgroup.mem_center_iff.mp
  Hint "The goal is now `{y} ∈ Subgroup.center G`. You have
  `h : ∀ (x : G), x ∈ Subgroup.center G`, so `h {y}` closes it."
  Hint (hidden := true) "`exact h {y}`"
  exact h y

Conclusion
"
Together with Level 5, you've shown both directions:
- **Forward** (L05): CommGroup → center = ⊤
- **Backward** (L06): center = ⊤ → commutativity

The proof had three short steps:
1. `rw [Subgroup.eq_top_iff'] at h` — extract universal membership
2. `apply Subgroup.mem_center_iff.mp` — reduce commutativity to center membership
3. `exact h y` — use `h` to provide the membership

The `apply` step uses a general pattern: when you have an iff
`h : P ↔ Q` and the goal matches `Q`, then `apply h.mp` changes
the goal to `P`. Here, `mem_center_iff.mp` takes center membership
and produces commutativity, so `apply` transforms the commutativity
goal into a center membership goal.

On paper: *\"If `Z(G) = G`, then `y ∈ Z(G)`, so `xy = yx`.\"*

In the boss, you'll combine both directions into a single `↔` proof
using the **split-and-recombine** pattern from Level 5.
"
