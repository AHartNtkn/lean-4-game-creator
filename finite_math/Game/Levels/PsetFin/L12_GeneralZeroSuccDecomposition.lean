import Game.Metadata

World "PsetFin"
Level 12

Title "The Dual Decomposition"

Introduction "
# General 0/succ Decomposition

In Level 11, you proved the general **castSucc/last decomposition**:
every element of `Fin (n + 1)` is either `Fin.last n` or
`j.castSucc` for some `j`.

The course has emphasized that castSucc/last and 0/succ are **dual**
decompositions — mirror images of each other. But so far, you've
only proved the 0/succ decomposition concretely for `Fin 3`
(FinNavigation Level 10). Here you'll prove it for general `n`.

The proof mirrors L11's structure: instead of splitting on
`v = n` vs `v < n`, you split on `v = 0` vs `v >= 1`.
- If `v = 0`: the element is `0`
- If `v >= 1`: the element is `j.succ` where `j = (v - 1, proof)`

**Your task**: Prove the general 0/succ decomposition.
"

/-- Every element of Fin (n+1) is either 0 or a successor. -/
Statement (n : ℕ) : ∀ i : Fin (n + 1), i = 0 ∨ ∃ j : Fin n, i = j.succ := by
  Hint "Start with `intro i`, then destructure with
  `cases i with | mk v hv =>`."
  intro i
  cases i with
  | mk v hv =>
    Hint "Now case-split on `v` itself: `cases v with | zero => ... | succ m => ...`"
    cases v with
    | zero =>
      Hint "Here `v = 0`, so `i = 0`. Choose `left` and use `rfl`."
      Hint (hidden := true) "`left; rfl`"
      left
      rfl
    | succ m =>
      Hint "Here `v = m + 1`, so `i = j.succ` where `j = ⟨m, ...⟩ : Fin n`.
      Choose `right`, provide the witness, then prove via `ext` + `Fin.val_succ`."
      Hint (hidden := true) "`right; use ⟨m, by omega⟩; ext; rw [Fin.val_succ]`"
      right
      use ⟨m, by omega⟩
      ext
      rw [Fin.val_succ]

Conclusion "
You've completed the **dual** of Level 11:

| Decomposition | General proof | Splits on |
|---|---|---|
| castSucc/last (L11) | `v = n` or `v < n` | Top boundary |
| 0/succ (this level) | `v = 0` or `v >= 1` | Bottom boundary |

The **value repackaging** pattern appeared again: `use ⟨m, by omega⟩`
takes the predecessor value and repackages it into `Fin n`.

Both decompositions are now proved for arbitrary `n`. This
symmetry is fundamental: it's why tuples can be built from
*either end* — `Fin.cons` routes through `0`/`succ` (prepend),
`vecSnoc` routes through `castSucc`/`last` (append).

In Mathlib, this decomposition is packaged as `Fin.cases` —
the 0/succ dual of `Fin.lastCases`.

There's a unifying concept behind both decompositions:
`Fin.succAbove p` is an embedding `Fin n -> Fin (n+1)` that
'skips' position `p`. When `p = Fin.last n`, `succAbove` is
`castSucc` (skip the last position). When `p = 0`, `succAbove`
is `succ` (skip position 0). Both `castSucc` and `succ` are
special cases of the same 'skip one position' operation. This
means the castSucc/last and 0/succ decompositions are both
instances of a single pattern: decompose `Fin (n+1)` into the
image of `succAbove p` plus the singleton `{p}`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Fin.cases Fin.eq_zero_or_eq_succ
