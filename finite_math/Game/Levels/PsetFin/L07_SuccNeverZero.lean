import Game.Metadata

World "PsetFin"
Level 7

Title "Abstract Successor Separation"

Introduction "
# Successors Are Never Zero

In FinNavigation, you proved that `i.succ ≠ 0` for elements of
`Fin 3`. Here you'll prove the same fact **for all `n`**.

The proof strategy is the same value reasoning pattern:
1. Assume `i.succ = 0`
2. Convert to values with `Fin.ext_iff`
3. Simplify both sides with `Fin.val_succ` and `Fin.val_zero`
4. Derive a contradiction
"

/-- No successor equals zero, for any Fin type. -/
Statement (n : ℕ) (i : Fin n) : i.succ ≠ (0 : Fin (n + 1)) := by
  Hint "Start with `intro h` to assume the equality."
  intro h
  Hint "Convert to values: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify both sides: `rw [Fin.val_succ, Fin.val_zero] at h`."
  Hint (hidden := true) "After the rewrite, the hypothesis says
  `i.val + 1 = 0`. This is impossible for natural numbers. `omega`
  closes the goal."
  rw [Fin.val_succ, Fin.val_zero] at h
  omega

Conclusion "
The same proof from FinNavigation works with abstract `n` — the
pattern doesn't depend on the specific type.

This is the **0/succ separation**: the image of `succ` (values
`1, ..., n`) and the singleton `0` (value `0`) are disjoint.
Combined with Level 2's abstract castSucc/last separation,
you now have both separation facts in full generality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Fin.succ_pos Fin.succ_ne_zero
