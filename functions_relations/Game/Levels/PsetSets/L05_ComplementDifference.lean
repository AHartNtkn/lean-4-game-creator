import Game.Metadata

World "PsetSets"
Level 5

Title "Complement-Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 5

Prove that `tᶜ \\ sᶜ ⊆ s \\ t`. In words: if `x` is NOT in `t` and
IS NOT in `sᶜ` (= it IS in `s`), then `x ∈ s \\ t`.

The twist: extracting `x ∈ s` from `x ∉ sᶜ` requires double negation
elimination — you will need `by_contra`.

**What is happening logically**: `tᶜ \\ sᶜ` means `x ∉ t ∧ ¬(x ∉ s)`,
and `s \\ t` means `x ∈ s ∧ x ∉ t`. To get `x ∈ s` from `¬(x ∉ s)`,
assume `x ∉ s` and derive a contradiction.
"

/-- The complement of a difference is contained in the reversed difference. -/
Statement (α : Type) (s t : Set α) : tᶜ \ sᶜ ⊆ s \ t := by
  Hint "Start with `intro x hx` then `obtain ⟨hnt, hnns⟩ := hx` to
  destructure the set difference."
  intro x hx
  obtain ⟨hnt, hnns⟩ := hx
  Hint "You have `hnt : x ∈ tᶜ` (= `x ∉ t`) and `hnns : x ∉ sᶜ`
  (= `¬(x ∉ s)`). Build `x ∈ s \\ t` with `constructor`."
  constructor
  · Hint "You need `x ∈ s`. You have `hnns : ¬(x ∉ s)`, which is
    double-negated membership. Use `by_contra h` to assume `x ∉ s`."
    Hint (hidden := true) "`by_contra h` gives `h : x ∉ s`. Then
    `exact hnns h` — applying `hnns` to `h` gives `False`."
    by_contra h
    exact hnns h
  · Hint "`hnt` is exactly what you need."
    exact hnt

Conclusion "
You extracted membership from double negation using `by_contra`:

```
by_contra h     -- h : x ∉ s
exact hnns h    -- hnns : ¬(x ∉ s) applied to h gives False
```

This is the same classical reasoning from Set Operations World (double
complement, De Morgan), now applied in a set-difference context. The
pattern: when you need `P` but only have `¬¬P`, assume `¬P` and
derive a contradiction.

**Next level**: The converse `s \\ t ⊆ tᶜ \\ sᶜ` also holds — you
will prove it in Level 6. Together they give `tᶜ \\ sᶜ = s \\ t`.
The surprise: the converse does NOT need `by_contra`.
"

/-- `compl_sdiff_compl` states `xᶜ \\ yᶜ = y \\ x`. -/
TheoremDoc compl_sdiff_compl as "compl_sdiff_compl" in "Set"

/-- `not_not` states `¬¬a ↔ a` (double negation elimination). -/
TheoremDoc not_not as "not_not" in "Set"

/-- `Decidable.not_not` is the decidable version of double negation elimination. -/
TheoremDoc Decidable.not_not as "Decidable.not_not" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf compl_sdiff_compl not_not Decidable.not_not
