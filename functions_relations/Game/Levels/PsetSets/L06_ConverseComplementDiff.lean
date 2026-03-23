import Game.Metadata

World "PsetSets"
Level 6

Title "Converse Complement-Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 6

In Level 5, you proved `tc \\ sc ⊆ s \\ t` using `by_contra` to
extract membership from double negation. Now prove the **converse**:

$$s \\setminus t \\subseteq t^c \\setminus s^c$$

The surprise: this direction does NOT need `by_contra`. It goes
through directly! If `x in s` and `x notin t`, then `x in tc`
(because `x notin t`) and `x notin sc` (because `x in s`).

Together with Level 5, this gives the full equality
`tc \\ sc = s \\ t` — but the two directions have genuinely different
proof structures. One needs classical reasoning; the other does not.
"

/-- The converse: s \\ t ⊆ tᶜ \\ sᶜ. -/
Statement (α : Type) (s t : Set α) : s \ t ⊆ tᶜ \ sᶜ := by
  Hint "Start with `intro x hx` then `obtain` to destructure the
  set difference."
  intro x hx
  obtain ⟨hs, hnt⟩ := hx
  Hint "You have `hs : x ∈ s` and `hnt : x ∉ t`. Build
  `x ∈ tᶜ \\ sᶜ`, which is `x ∈ tᶜ ∧ x ∉ sᶜ`. Use `constructor`."
  Hint (hidden := true) "Key move: `constructor` splits the goal. The
  first part is `hnt` (since `x ∈ tᶜ` means `x ∉ t`). The second part
  needs `intro hns; exact hns hs`."
  constructor
  · Hint "`x ∈ tᶜ` means `x ∉ t`. You have `hnt`."
    exact hnt
  · Hint "You need `x ∉ sᶜ`, i.e., `¬(x ∉ s)`. Introduce the assumption
    and use `hs` for the contradiction."
    Hint (hidden := true) "`intro hns` then `exact hns hs`."
    intro hns
    exact hns hs

Conclusion "
You proved the converse `s \\ t ⊆ tᶜ \\ sᶜ` — and it was entirely
direct. No `by_contra` needed!

**Proof asymmetry**: Compare the two directions:
- Level 5 (`tᶜ \\ sᶜ ⊆ s \\ t`): needed `by_contra` to extract
  `x ∈ s` from `¬(x ∉ s)` — double negation elimination
- This level (`s \\ t ⊆ tᶜ \\ sᶜ`): direct — `x ∈ s` gives
  `¬(x ∉ s)` by simply introducing the assumption and applying

This asymmetry is fundamental: going from `P` to `¬¬P` is
constructive (always valid), but going from `¬¬P` to `P` requires
classical logic (`by_contra`). Both directions are true, but they
have different logical character.

Together: `tᶜ \\ sᶜ = s \\ t`. You could prove this full equality in
one line using `Set.Subset.antisymm` from Level 5 and this level — the
same technique as Level 4 of Subset World. Complement-difference is its
own inverse in a precise sense.
"

/-- `compl_sdiff_compl` states `xᶜ \\ yᶜ = y \\ x`. -/
TheoremDoc compl_sdiff_compl as "compl_sdiff_compl" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf compl_sdiff_compl
