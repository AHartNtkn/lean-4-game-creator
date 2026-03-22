import Game.Metadata

World "PsetFin"
Level 1

Title "Two Distinct Witnesses"

Introduction "
# Problem Set: Fin Types

Welcome to your first problem set. You'll apply skills from
MeetFin, FinNavigation, and FinTuples to **fresh problems**
with sparser hints and no new definitions.

If you get stuck, ask yourself:
- Is the goal about **Fin elements being equal**? Try `ext`.
- Is the goal about **functions being equal**? Try `ext`.
- Is the goal about **values**? Try val lemmas + `omega`.
- Do you need to **enumerate cases**? Destructure + case split.
- Can you **reconstruct** a tuple? `cons_self_tail` or `vecSnoc_self_init`.

**Your task**: Find two distinct elements of `Fin 4` whose
values sum to 5.
"

/-- Two distinct Fin 4 elements whose values sum to 5. -/
Statement : ∃ i j : Fin 4, i ≠ j ∧ i.val + j.val = 5 := by
  Hint "Provide both witnesses at once with `use`.
  Which two numbers less than 4 sum to 5?"
  Hint (hidden := true) "Try `use ⟨2, by omega⟩, ⟨3, by omega⟩`."
  use ⟨2, by omega⟩, ⟨3, by omega⟩
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "Prove the two elements are unequal.
    Recall the pattern from MeetFin: `intro h; cases h`."
    Hint (hidden := true) "`intro h` assumes they're equal,
    then `cases h` sees the values differ and closes the goal."
    intro h; cases h
  · Hint (hidden := true) "Both sides compute to 5. Use `rfl`."
    rfl

Conclusion "
Two skills combined on a fresh problem:
- `use ⟨k, by omega⟩` for existential witnesses
- `intro h; cases h` for Fin inequality between concrete literals

The double `use` syntax — `use expr1, expr2` — fills
multiple existentials in one step.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
