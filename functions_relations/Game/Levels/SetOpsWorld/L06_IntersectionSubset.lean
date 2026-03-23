import Game.Metadata

World "SetOpsWorld"
Level 6

Title "Intersection and Subsets"

Introduction "
# s ∩ t ⊆ s

You know that `∩` means `∧`. It follows immediately that the
intersection of two sets is a subset of each:

$$s \\cap t \\subseteq s$$

because if `x ∈ s ∧ x ∈ t`, then certainly `x ∈ s`.

**Your task**: Prove this formally. The proof combines the `⊆` proof
shape (`intro x hx`) with extraction from an intersection hypothesis.

Since `hx : x ∈ s ∩ t` is definitionally a conjunction, you can
extract the left component with `hx.1` — the same dot projection
you used on `∧` in Subset World.
"

/-- The intersection of two sets is a subset of the first. -/
Statement (α : Type) (s t : Set α) : s ∩ t ⊆ s := by
  Hint "The goal is `s ∩ t ⊆ s`, which means `∀ x, x ∈ s ∩ t → x ∈ s`.
  Start with `intro x hx`."
  intro x hx
  Hint "`hx : x ∈ s ∩ t` is definitionally `x ∈ s ∧ x ∈ t`.
  You need `x ∈ s`, which is the left component.
  Use `exact hx.1` to extract it."
  Hint (hidden := true) "`exact hx.1` — the `.1` projection extracts
  the first component of the conjunction.

  Alternatively: `obtain ⟨hs, _⟩ := hx` then `exact hs`."
  Branch
    obtain ⟨hs, _⟩ := hx
    exact hs
  Branch
    change x ∈ s ∧ x ∈ t at hx
    exact hx.1
  exact hx.1

Conclusion "
A one-line extraction: `hx.1` pulls out the left component of an
intersection hypothesis, just as it does for any conjunction.

This fact — `s ∩ t ⊆ s` — is called `Set.inter_subset_left` in the
library. The symmetric version `s ∩ t ⊆ t` (using `.2`) is
`Set.inter_subset_right`.

The proof shape is worth remembering: when you have a hypothesis
with more information than you need (like `x ∈ s ∩ t` when you only
need `x ∈ s`), just project out the relevant component.
"

/-- `Set.inter_subset_left` proves `s ∩ t ⊆ s` — the intersection
is a subset of the first set.

## Statement
```
Set.inter_subset_left : s ∩ t ⊆ s
```

## Proof idea
If `x ∈ s ∩ t` then `x ∈ s ∧ x ∈ t`, so in particular `x ∈ s`.
-/
TheoremDoc Set.inter_subset_left as "Set.inter_subset_left" in "Set"

/-- `Set.inter_subset_right` proves `s ∩ t ⊆ t`. -/
TheoremDoc Set.inter_subset_right as "Set.inter_subset_right" in "Set"

/-- `inf_le_left` is the lattice version of `s ∩ t ⊆ s`. -/
TheoremDoc inf_le_left as "inf_le_left" in "Set"

/-- `inf_le_right` is the lattice version of `s ∩ t ⊆ t`. -/
TheoremDoc inf_le_right as "inf_le_right" in "Set"

NewTheorem Set.inter_subset_left

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_subset_left Set.inter_subset_right inf_le_left inf_le_right
