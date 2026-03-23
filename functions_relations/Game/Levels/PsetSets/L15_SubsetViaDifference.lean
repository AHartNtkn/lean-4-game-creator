import Game.Metadata

World "PsetSets"
Level 15

Title "Subset via Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 15

Prove a fundamental characterization of subset in terms of set
difference:

$$s \\subseteq t \\;\\iff\\; s \\setminus t = \\emptyset$$

In words: `s` is contained in `t` if and only if there are no elements
in `s` that are not in `t` — i.e., the set difference `s \\ t` is empty.

Think about each direction: what does the hypothesis give you, and what
do you need to show? The two directions have different proof structures.
"

/-- Subset is characterized by empty set difference. -/
Statement (α : Type) (s t : Set α) : s ⊆ t ↔ s \ t = ∅ := by
  Hint "Use `constructor` to split the biconditional into two directions."
  constructor
  -- Forward: s ⊆ t → s \ t = ∅
  · Hint "**Forward**: Given `h : s ⊆ t`, prove `s \\ t = ∅`. Use `ext x`
    then `constructor`."
    intro h
    ext x
    constructor
    · Hint "Given `x ∈ s \\ t`, derive `False`. Destructure the difference
      and use the subset hypothesis."
      Hint (hidden := true) "Key move: `intro hx; obtain ⟨hs, hnt⟩ := hx;
      exact hnt (h hs)` — `h hs` gives `x ∈ t`, contradicting `hnt`."
      intro hx
      obtain ⟨hs, hnt⟩ := hx
      exact hnt (h hs)
    · Hint "`x ∈ ∅` is `False`. Use `intro hx; exact hx.elim`."
      intro hx
      exact hx.elim
  -- Backward: s \ t = ∅ → s ⊆ t
  · Hint "**Backward**: Given `h : s \\ t = ∅`, prove `s ⊆ t`. Start with
    `intro x hx` as usual for a subset proof."
    intro h
    intro x hx
    Hint "You need `x ∈ t`. Use `by_contra hnt` to assume `x ∉ t`, then
    build `x ∈ s \\ t` and use the equality `h` to reach a contradiction."
    Hint (hidden := true) "Key move: `by_contra hnt` then
    `have hd : x ∈ s \\ t := ⟨hx, hnt⟩` then `rw [h] at hd` gives
    `hd : x ∈ ∅` (which is `False`). Close with `exact hd`."
    by_contra hnt
    have hd : x ∈ s \ t := ⟨hx, hnt⟩
    rw [h] at hd
    exact hd

Conclusion "
You proved `s ⊆ t ↔ s \\ t = ∅` — one of the most useful
characterizations of subset in practice.

**Forward**: If `s ⊆ t`, no element can be in `s` but not in `t`, so
`s \\ t` has no elements — it is `∅`.

**Backward**: If `s \\ t = ∅`, then for any `x ∈ s`, assuming `x ∉ t`
would place `x` in `s \\ t = ∅` — contradiction. So `x ∈ t`.

The backward direction used a key technique: **rewriting with a set
equality on a membership hypothesis**. After `rw [h] at hd`, the
hypothesis `hd : x ∈ s \\ t` becomes `hd : x ∈ ∅` (which is `False`),
immediately closing the goal. This `rw` on membership is a powerful
pattern you will see again.
"

/-- `Set.subset_empty_iff` states `s ⊆ ∅ ↔ s = ∅`. -/
TheoremDoc Set.subset_empty_iff as "Set.subset_empty_iff" in "Set"

/-- `Set.diff_eq_empty` states `s \\ t = ∅ ↔ s ⊆ t`. -/
TheoremDoc Set.diff_eq_empty as "Set.diff_eq_empty" in "Set"

/-- `sdiff_eq_bot_iff` is the lattice version: `a \\ b = ⊥ ↔ a ≤ b`. -/
TheoremDoc sdiff_eq_bot_iff as "sdiff_eq_bot_iff" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.subset_empty_iff Set.diff_eq_empty sdiff_eq_bot_iff
