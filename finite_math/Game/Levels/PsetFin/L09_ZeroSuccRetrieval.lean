import Game.Metadata

World "PsetFin"
Level 9

Title "From Nonzero to Successor"

Introduction "
# The 0/succ Decomposition Applied

In FinNavigation, you proved that every element of `Fin (n+1)` is
either `0` or `j.succ` for some `j`. Here's the applied version:
given that `i` is not zero, prove it must be a successor.

**Strategy**: Destructure `i` into its value and bound, case-split
on the value:
- If `v = 0`: contradiction with `i /= 0`
- If `v = succ n`: provide the witness
"

/-- A nonzero Fin element is a successor image. -/
Statement (i : Fin 4) (h : i ≠ 0) : ∃ j : Fin 3, i = j.succ := by
  Hint "Destructure `i` into its value and bound."
  Hint (hidden := true) "`cases i with | mk v hv =>`"
  cases i with
  | mk v hv =>
    Hint "Case-split on `v`: is it zero or a successor?"
    Hint (hidden := true) "`cases v with | zero => ... | succ n => ...`"
    cases v with
    | zero =>
      Hint "Here `v = 0`, so `i = 0`. But `h` says `i /= 0`.
      Use `exact absurd rfl h`."
      exact absurd rfl h
    | succ n =>
      Hint "Here `v = n + 1`. Provide the preimage and prove equality."
      Hint (hidden := true) "`use ⟨n, by omega⟩; ext; rw [Fin.val_succ]`"
      use ⟨n, by omega⟩
      ext
      rw [Fin.val_succ]

Conclusion "
This is the 0/succ decomposition in applied form: if an element
isn't `0`, it must be `j.succ` for some `j`. Combined with the
succ /= 0 fact from Level 7, the decomposition is **disjoint** —
an element is either 0 or a successor, never both.

The proof pattern:
1. Destructure into value and bound
2. Case-split on the value
3. Zero case: contradiction with the hypothesis
4. Succ case: construct the witness
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
