import Game.Metadata

World "MeetFin"
Level 18

Title "Case Analysis Practice"

Introduction "
# Practice: Case Analysis on Fin 3

In Level 17, you exhausted all cases of `Fin 2` (two valid, one
impossible). Now try `Fin 3` — the same strategy with one more valid
case.

**Why are some tactics disabled?** You might wonder why tactics like
`fin_cases`, `decide`, and `norm_num` are unavailable. These tactics
can automate case analysis and arithmetic in one step — which is
exactly why they're disabled here. The manual approach forces you to
understand *what* the automation does: destructure the `Fin` element,
split on the natural number, handle each valid case, and dismiss
impossible cases with `absurd`. Once you understand this structure,
you'll appreciate the automation when it's unlocked later. The
automation doesn't replace this understanding — it just lets you
skip the mechanical parts once you've mastered them.

The pattern is the same:
1. **Destructure**: `cases x with | mk v hlt =>`
2. **Case-split on `v`**: `cases v with | zero => ... | succ n => ...`
3. **Nest further** as needed
4. **Valid cases**: `left`/`right` + `rfl`
5. **Impossible cases**: `exact absurd hlt (by omega)`

For `Fin 3`, you'll have three valid cases (`v = 0, 1, 2`) and one
impossible case (`v ≥ 3`).

**Your task**: Prove that every element of `Fin 3` is `0`, `1`, or `2`.
"

/-- Every element of `Fin 3` is `0`, `1`, or `2`. -/
Statement (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  Hint "Start by destructuring: `cases x with | mk v hlt =>`"
  cases x with
  | mk v hlt =>
    Hint "Case-split on `v`: `cases v with | zero => ... | succ n => ...`"
    cases v with
    | zero =>
      Hint "Here `v = 0`. Choose the left disjunct: `left` then `rfl`."
      left
      rfl
    | succ n =>
      Hint "Now `v = n + 1`. Case-split again on `n`."
      cases n with
      | zero =>
        Hint "Here `v = 1`. Choose `right` then `left` then `rfl`."
        right
        left
        rfl
      | succ m =>
        Hint "Now `v = m + 2`. One more case split on `m`."
        cases m with
        | zero =>
          Hint "Here `v = 2`. Choose `right` then `right` then `rfl`."
          right
          right
          rfl
        | succ k =>
          Hint (hidden := true) "Here `v = k + 3` but `hlt` says `v < 3`.
          This is impossible: `exact absurd hlt (by omega)`."
          exact absurd hlt (by omega)

Conclusion "
You've now done case analysis on both `Fin 2` (Level 17) and `Fin 3`.

The pattern scales: for `Fin n`, you get `n` valid cases and one
impossible case. Each additional `n` adds one more nesting level.

For large `n`, this would be tedious. That's why the `fin_cases`
tactic (currently disabled) exists — it automates the entire case
split. You'll unlock it in a later world.

You've now verified by case analysis that `Fin 0` has 0 elements,
`Fin 1` has 1, `Fin 2` has 2, and `Fin 3` has 3. The general fact —
`Fin n` has exactly `n` elements — will be formalized using
`Fintype.card` in the Cardinality world.

This practice prepares you for the boss, where you'll combine case
analysis with other moves.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Fin.forall_fin_two
