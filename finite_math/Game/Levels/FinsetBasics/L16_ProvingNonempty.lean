import Game.Metadata

World "FinsetBasics"
Level 16

Title "Proving Nonempty"

Introduction "
# Proving Nonempty

In the previous level, you **extracted** an element from a nonempty
finset using `obtain`. Now you'll go the other direction: **proving**
that a finset is nonempty.

Since `s.Nonempty` means `∃ x, x ∈ s`, you prove it by:
1. `use a` — provide a specific element `a` as the witness
2. Prove `a ∈ s` — show the witness is actually in the finset

This combines the existential witness move (`use`) with the
membership proof move (`rw [Finset.mem_insert]` + `left`/`right`)
from earlier levels.

**Your task**: Prove that `{1, 2, 3}` is nonempty.
"

/-- The finset {1, 2, 3} is nonempty. -/
Statement : Finset.Nonempty ({1, 2, 3} : Finset ℕ) := by
  Hint "The goal is `Nonempty`, which means `∃ x, x ∈ s`.
  Provide a witness with `use 1`."
  use 1
  Hint "Now prove membership of `1` in the finset. This is the same
  proof from Level 1: `rw [Finset.mem_insert]` then `left; rfl`."
  Hint (hidden := true) "`rw [Finset.mem_insert]; left; rfl`"
  rw [Finset.mem_insert]
  left
  rfl

Conclusion "
You now know both directions of `Finset.Nonempty`:

| Direction | Pattern | When to use |
|---|---|---|
| Backward (extract) | `obtain ⟨x, hx⟩ := hs` | When you have `hs : s.Nonempty` and need an element |
| Forward (construct) | `use a` then prove `a ∈ s` | When you need to prove `s.Nonempty` |

The forward direction combines two moves you already know:
existential witness (`use`) and membership proof (the insert
peeling chain). The boss will test this combination.

In ordinary mathematics: 'the set is nonempty because it contains 1.'
In Lean: `use 1; prove 1 ∈ s`.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.insert_nonempty Finset.singleton_nonempty Finset.mem_insert_self Finset.mem_insert_of_mem
