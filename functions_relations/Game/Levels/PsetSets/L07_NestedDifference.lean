import Game.Metadata

World "PsetSets"
Level 7

Title "Nested Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 7

Prove the identity `s \\ (s \\ t) = s ∩ t`.

In words: removing from `s` everything that is in `s` but not in `t`
leaves exactly `s ∩ t` — the elements that are in BOTH sets.

This is the longest proof in the problem set so far. Each individual
step is familiar; the challenge is combining them correctly in a
nested context.
"

/-- Subtracting a difference recovers the intersection. -/
Statement (α : Type) (s t : Set α) : s \ (s \ t) = s ∩ t := by
  Hint "Use `ext x` then `constructor` to start the set equality proof."
  ext x
  constructor
  -- Forward: s \ (s \ t) → s ∩ t
  · Hint "**Forward**: `x ∈ s \\ (s \\ t)` means `x ∈ s` and
    `x ∉ s \\ t` (= `¬(x ∈ s ∧ x ∉ t)`). You need `x ∈ s ∩ t`.
    Start with `intro hx` then `obtain ⟨hs, hd⟩ := hx`."
    intro hx
    obtain ⟨hs, hd⟩ := hx
    Hint "You have `hs : x ∈ s` and `hd : x ∉ s \\ t`. Use `constructor`
    to split the intersection goal."
    constructor
    · Hint "`hs` gives the first component directly."
      exact hs
    · Hint "You need `x ∈ t`. The hypothesis `hd` says `¬(x ∈ s ∧ x ∉ t)`.
      Since `x ∈ s` is known, if `x ∉ t` then `x ∈ s ∧ x ∉ t` holds,
      contradicting `hd`. Use `by_contra`."
      Hint (hidden := true) "`by_contra hnt` gives `hnt : x ∉ t`. Then
      `exact hd ⟨hs, hnt⟩` constructs the contradiction."
      by_contra hnt
      exact hd ⟨hs, hnt⟩
  -- Backward: s ∩ t → s \ (s \ t)
  · Hint "**Backward**: `x ∈ s ∩ t` means `x ∈ s ∧ x ∈ t`. You need
    `x ∈ s \\ (s \\ t)`, which is `x ∈ s ∧ x ∉ s \\ t`. Start with
    `intro hx` then `obtain ⟨hs, ht⟩ := hx`."
    intro hx
    obtain ⟨hs, ht⟩ := hx
    Hint "Use `constructor`. The first part is `x ∈ s` (from `hs`).
    The second part is `x ∉ s \\ t` — introduce the assumption and
    find a contradiction."
    constructor
    · exact hs
    · Hint "You need `x ∉ s \\ t`, i.e., `(x ∈ s ∧ x ∉ t) → False`.
      Use `intro hst` to assume `x ∈ s \\ t`."
      Hint (hidden := true) "`intro hst` then `exact hst.2 ht` — the second
      component of `hst` says `x ∉ t`, contradicting `ht : x ∈ t`."
      intro hst
      exact hst.2 ht

Conclusion "
You proved `s \\ (s \\ t) = s ∩ t`. The key insight in the forward
direction: knowing that `x ∈ s` and `¬(x ∈ s ∧ x ∉ t)` implies
`x ∈ t` — because if `x ∉ t`, then `x ∈ s ∧ x ∉ t` holds,
contradicting the second hypothesis.

This is the same `by_contra` pattern from Level 5, applied at a
deeper nesting level. When you see a negated conjunction and already
know one conjunct, `by_contra` on the other conjunct gives you the
full conjunction to feed into the negation.

The backward direction was simpler: `hst.2` extracts `x ∉ t` from
`x ∈ s \\ t`, and `ht` provides the contradiction.
"

/-- `sdiff_sdiff_right_self` states `x \\ (x \\ y) = x ⊓ y`. -/
TheoremDoc sdiff_sdiff_right_self as "sdiff_sdiff_right_self" in "Set"

/-- `sdiff_sdiff_eq_self` states `x \\ (x \\ y) = y` when `y ≤ x`. -/
TheoremDoc sdiff_sdiff_eq_self as "sdiff_sdiff_eq_self" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf sdiff_sdiff_right_self sdiff_sdiff_eq_self
