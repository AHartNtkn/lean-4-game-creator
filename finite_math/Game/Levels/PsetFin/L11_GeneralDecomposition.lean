import Game.Metadata

World "PsetFin"
Level 11

Title "The General Decomposition"

Introduction "
# From Concrete to Abstract

In the FinNavigation boss, you proved that every element of
`Fin 3` is either `Fin.last 2` or `j.castSucc` for some `j`.
That proof used exhaustive case analysis on all three values.

Here you'll prove the **general** version: for ANY `n`, every
element of `Fin (n + 1)` is either `Fin.last n` or `j.castSucc`.

The proof uses a different strategy. Instead of checking each
value, you split on whether `i.val = n` or `i.val < n`:
- If `i.val = n`: then `i = Fin.last n` (by `ext` + `Fin.val_last`)
- If `i.val < n`: then `i = j.castSucc` where `j = (i.val, proof)` (the L13 pattern from FinNavigation)

The key insight: `i.val < n + 1` (from `i.isLt`) means either
`i.val < n` or `i.val = n`. You can derive this disjunction
with `omega` and then case-split on it.
"

/-- Every element of Fin (n+1) is either last or a castSucc image. -/
Statement (n : ℕ) : ∀ i : Fin (n + 1), i = Fin.last n ∨ ∃ j : Fin n, i = j.castSucc := by
  Hint "Start with `intro i`, then destructure with
  `cases i with | mk v hv =>`."
  intro i
  cases i with
  | mk v hv =>
    Hint "Now `v < n + 1`. This means either `v < n` or `v = n`.
    Create this disjunction: `have h : v < n or v = n := by omega`."
    Hint (hidden := true) "`have h : v < n or v = n := by omega`"
    have h : v < n ∨ v = n := by omega
    Hint "Case-split on `h`: `cases h with | inl hlt => ... | inr heq => ...`"
    cases h with
    | inl hlt =>
      Hint "Here `v < n`, so the element is a `castSucc` image.
      Choose `right` and provide the witness."
      Hint (hidden := true) "`right; use ⟨v, hlt⟩; ext; rw [Fin.val_castSucc]`"
      right
      use ⟨v, hlt⟩
      ext
      rw [Fin.val_castSucc]
    | inr heq =>
      Hint "Here `v = n`, so the element IS `Fin.last n`.
      Choose `left` and prove the equality."
      Hint (hidden := true) "`left; ext; rw [Fin.val_last]; exact heq`"
      left
      ext
      rw [Fin.val_last]
      exact heq

Conclusion "
You've generalized the concrete decomposition to ALL `n`.

The concrete proof (FinNavigation boss) worked by checking every
value of `Fin 3`. The abstract proof works by splitting on
`v < n or v = n` — a fact `omega` can derive from `v < n + 1`.

Notice the **value repackaging** pattern (from FinNavigation L13):
`use ⟨v, hlt⟩` takes the same value `v` and justifies it in
`Fin n` with the new bound `hlt : v < n`. The value doesn't
change — only the type's upper bound shrinks.

This is the first taste of **generalizing from concrete to
abstract**: the same structural fact holds, but the proof strategy
changes from exhaustive enumeration to case analysis on a
disjunction. This pattern appears throughout mathematics — concrete
examples reveal the structure, but general proofs use different
(often cleaner) strategies.

(In Mathlib, this decomposition is packaged as `Fin.lastCases` —
an eliminator that lets you handle the last element and castSucc
images separately. You just proved the underlying fact by hand.)
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Fin.lastCases Fin.reverseInduction
