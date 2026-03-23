import Game.Metadata

World "PsetSets"
Level 14

Title "Complement of Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 14

Prove that the complement of a set difference equals the complement
union the removed set:

$$(s \\setminus t)^c = s^c \\cup t$$

In words: an element is NOT in `s \\ t` precisely when it is either
not in `s` at all, or it is in `t`.
"

/-- The complement of a difference: (s \\ t)ᶜ = sᶜ ∪ t. -/
Statement (α : Type) (s t : Set α) : (s \ t)ᶜ = sᶜ ∪ t := by
  Hint "Start with `ext x` then `constructor` for the set equality."
  ext x
  constructor
  -- Forward: x ∈ (s \ t)ᶜ → x ∈ sᶜ ∪ t
  · Hint "**Forward**: `x ∈ (s \\ t)ᶜ` means `¬(x ∈ s ∧ x ∉ t)`. You
    need `x ∈ sᶜ ∪ t`, i.e., `x ∉ s ∨ x ∈ t`. You cannot choose a side
    directly — use `by_contra` then `push_neg`."
    intro hx
    Hint "If you try `push_neg` directly on the goal, it will not make
    progress — `push_neg` works on explicit logical connectives, but the
    goal is wrapped in set complement and union notation. You need
    `by_contra` first, then `change` to expose the logical structure,
    then `push_neg`."
    Hint (hidden := true) "Key move: `by_contra h` then
    `change ¬(x ∉ s ∨ x ∈ t) at h` then `push_neg at h`."
    by_contra h
    Hint "After `by_contra h`, the hypothesis `h` has type
    `¬(x ∈ sᶜ ∪ t)`, which is `¬(x ∉ s ∨ x ∈ t)`. Use
    `change ¬(x ∉ s ∨ x ∈ t) at h` to expose this logical structure,
    then `push_neg at h` to convert to a conjunction."
    change ¬(x ∉ s ∨ x ∈ t) at h
    push_neg at h
    Hint "`push_neg` converted `¬(x ∉ s ∨ x ∈ t)` to `x ∈ s ∧ x ∉ t`.
    But `hx` says `¬(x ∈ s ∧ x ∉ t)` — contradiction."
    exact hx h
  -- Backward: x ∈ sᶜ ∪ t → x ∈ (s \ t)ᶜ
  · Hint "**Backward**: Given `x ∈ sᶜ ∪ t`, prove `x ∈ (s \\ t)ᶜ`,
    i.e., `¬(x ∈ s ∧ x ∉ t)`. Introduce the union, then assume
    `x ∈ s \\ t` and find a contradiction."
    intro hx
    Hint "The goal is `x ∈ (s \\ t)ᶜ`, which means `x ∉ s \\ t`. Use
    `intro hd` to assume `x ∈ s \\ t`, then destructure and case-split."
    Hint (hidden := true) "Key move: `intro hd` assumes the difference
    membership, then `cases hx` to find which case contradicts."
    intro hd
    obtain ⟨hs, hnt⟩ := hd
    cases hx with
    | inl hns =>
      Hint (hidden := true) "`hns : x ∉ s` contradicts `hs : x ∈ s` — use `exact hns hs`."
      exact hns hs
    | inr ht =>
      Hint (hidden := true) "`ht : x ∈ t` contradicts `hnt : x ∉ t` — use `exact hnt ht`."
      exact hnt ht

Conclusion "
You proved `(s \\ t)ᶜ = sᶜ ∪ t` using a three-step strategy that
will appear repeatedly in this problem set.

**The contrapositive extraction pattern** (`by_contra` + `change` +
`push_neg`):
1. `by_contra h` — assume the goal is false
2. `change` — expose the logical structure hidden under set notation
3. `push_neg at h` — convert the negation to a positive statement
4. The result contradicts the original hypothesis

This pattern applies whenever the goal is a set membership wrapped in
notation that `push_neg` cannot penetrate directly. You used the same
strategy in Levels 5 and 7.

**Backward direction**: Direct case analysis — each case of the union
contradicts one component of the assumed difference membership.

This identity says: the elements NOT removed by `s \\ t` are exactly
those that were never in `s` (in `sᶜ`) or were in `t` (so not removed).
"

/-- `compl_sdiff` states `(x \\ y)ᶜ = x ⇨ y` (Heyting implication). -/
TheoremDoc compl_sdiff as "compl_sdiff" in "Set"

/-- `himp_eq` states `x ⇨ y = y ⊔ xᶜ` in a Boolean algebra. -/
TheoremDoc himp_eq as "himp_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf compl_sdiff himp_eq
