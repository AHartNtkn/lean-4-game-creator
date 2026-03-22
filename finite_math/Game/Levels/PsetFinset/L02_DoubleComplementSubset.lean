import Game.Metadata

World "PsetFinset"
Level 2

Title "Double Complement Under Subset"

Introduction "
# Set Difference with a Subset Constraint

When $t \\subseteq s$, the double complement simplifies:

$$s \\setminus (s \\setminus t) = t$$

Removing from $s$ everything not in $t$, then taking that away
from $s$, recovers exactly $t$ (not just $s \\cap t$, because
every element of $t$ is already in $s$).

This is an `ext` proof. The **backward direction** will require
`by_contra` — you'll need to derive `x \\in t` from a negated
hypothesis.
"

/-- Under subset, double complement recovers the subset exactly. -/
Statement (s t : Finset ℕ) (hts : t ⊆ s) : s \ (s \ t) = t := by
  Hint (hidden := true) "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ s \ (s \ t) → x ∈ t
  · Hint "Use `intro h` and unfold with `rw [Finset.mem_sdiff] at h`."
    intro h
    rw [Finset.mem_sdiff] at h
    obtain ⟨hs, hst⟩ := h
    Hint "You have `hs : x ∈ s` and `hst : x ∉ s \\\\ t`. The goal
    is `x ∈ t` — a positive statement you can't extract directly."
    Hint (hidden := true) "Use `by_contra hnt` to assume `x ∉ t`.
    Then build `x ∈ s \\\\ t` from `hs` and `hnt` to contradict `hst`:
    `apply hst; rw [Finset.mem_sdiff]; exact ⟨hs, hnt⟩`."
    by_contra hnt
    apply hst
    rw [Finset.mem_sdiff]
    exact ⟨hs, hnt⟩
  -- Backward: x ∈ t → x ∈ s \ (s \ t)
  · Hint (hidden := true) "Use `intro hxt`, then `rw [Finset.mem_sdiff]`
    and `constructor`. First part: use `hts` to get `x ∈ s`.
    Second part: `intro h; rw [Finset.mem_sdiff] at h; exact h.2 hxt`."
    intro hxt
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.subset_iff] at hts
      exact hts hxt
    · intro h
      rw [Finset.mem_sdiff] at h
      exact h.2 hxt

Conclusion "
You proved $t \\subseteq s \\implies s \\setminus (s \\setminus t) = t$.

The forward direction required `by_contra`: the goal `x \\in t` is
positive, but your hypotheses only give `x \\in s` and
`x \\notin s \\setminus t`. Assuming `x \\notin t` lets you build
`x \\in s \\setminus t`, contradicting the second hypothesis.

The backward direction used the subset hypothesis to get `x \\in s`,
then showed `x \\in s \\setminus t` is impossible because it would
give `x \\notin t`.
"

/-- `Finset.inter_eq_right` states `s ∩ t = t ↔ t ⊆ s`. -/
TheoremDoc Finset.inter_eq_right as "Finset.inter_eq_right" in "Finset"

/-- `Finset.sdiff_sdiff_self_left` states `s \ (s \ t) = s ∩ t`. -/
TheoremDoc Finset.sdiff_sdiff_self_left as "Finset.sdiff_sdiff_self_left" in "Finset"

/-- `sdiff_sdiff_left` is a lattice lemma about iterated set difference. -/
TheoremDoc sdiff_sdiff_left as "sdiff_sdiff_left" in "Order"

/-- `sdiff_sdiff_eq_self` states `y ≤ x → x \ (x \ y) = y` in a Boolean algebra. -/
TheoremDoc sdiff_sdiff_eq_self as "sdiff_sdiff_eq_self" in "Order"

/-- `Finset.sdiff_sdiff_eq_self` states `t ⊆ s → s \ (s \ t) = t`. -/
TheoremDoc Finset.sdiff_sdiff_eq_self as "Finset.sdiff_sdiff_eq_self" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem sdiff_sdiff_right_self Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right inf_eq_right Finset.inter_eq_right Finset.sdiff_sdiff_self_left sdiff_sdiff_left sdiff_sdiff_eq_self Finset.sdiff_sdiff_eq_self
