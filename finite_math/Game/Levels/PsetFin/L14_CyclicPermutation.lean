import Game.Metadata

World "PsetFin"
Level 14

Title "Cyclic Permutation Has No Fixed Points"

Introduction "
# A Cyclic Permutation

In MeetFin, you saw that `Fin n` supports modular arithmetic —
addition wraps around. A natural example of this wrapping is the
**cyclic permutation** `![1, 2, 0] : Fin 3 -> Fin 3`.

This function shifts every element forward by one position, with
the last element wrapping back to 0:
- `0 -> 1`
- `1 -> 2`
- `2 -> 0`

A **fixed point** of a function `f` is an element `i` such that
`f i = i` — it doesn't move. The cyclic permutation has **no**
fixed points: every element moves.

**Your task**: Prove that `![1, 2, 0]` has no fixed points.

The strategy is case analysis on `Fin 3`: check each of the three
elements and verify that the output differs from the input.
"

/-- The cyclic permutation ![1, 2, 0] has no fixed points. -/
Statement : ∀ i : Fin 3, (![1, 2, 0] : Fin 3 → Fin 3) i ≠ i := by
  Hint "Start with `intro i` to take an arbitrary element of `Fin 3`,
  then destructure with `cases i with | mk v hv`."
  intro ⟨v, hv⟩
  Hint "Case-split on `v` to check each value:
  `cases v with | zero | succ n`"
  Hint (hidden := true) "For each valid value, the output differs
  from the input. Close with `intro h; cases h` for the contradiction."
  cases v with
  | zero =>
    Hint (hidden := true) "`![1, 2, 0] 0 = 1 /= 0`.
    Use `intro h; cases h`."
    intro h; cases h
  | succ n =>
    cases n with
    | zero =>
      Hint (hidden := true) "`![1, 2, 0] 1 = 2 /= 1`.
      Use `intro h; cases h`."
      intro h; cases h
    | succ m =>
      cases m with
      | zero =>
        Hint (hidden := true) "`![1, 2, 0] 2 = 0 /= 2`.
        Use `intro h; cases h`."
        intro h; cases h
      | succ k => exact absurd hv (by omega)

Conclusion "
You proved that the cyclic permutation `![1, 2, 0]` has no fixed
points — every element moves.

The proof used the same case-analysis-on-Fin pattern you've used
throughout Phase 1: destructure into `(v, hv)`, case-split on `v`,
and handle each valid case.

This is the cyclic structure mentioned in MeetFin's modular
arithmetic level: the permutation `0 -> 1 -> 2 -> 0` cycles
through all three positions before returning to the start.
Algebraically, this permutation generates the cyclic group
$\\mathbb{Z}/3\\mathbb{Z}$ — the same group structure as
addition modulo 3 on `Fin 3`.

This level exercises three skills on a single object:
- `vec_cons` evaluation (FinTuples) — reading `![1, 2, 0]` at each index
- Case analysis on `Fin 3` (MeetFin) — enumerating all elements
- Inequality via `cases h` (MeetFin) — proving the output differs
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
