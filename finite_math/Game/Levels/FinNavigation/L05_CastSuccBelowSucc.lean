import Game.Metadata

World "FinNavigation"
Level 5

Title "castSucc is Below succ"

Introduction "
# Combining Val Lemmas

You now know three val lemmas: `Fin.val_last`, `Fin.val_castSucc`,
and `Fin.val_succ`. Time to **combine** them.

If `i : Fin n`, then `i.castSucc` and `i.succ` both live in
`Fin (n+1)`. Which one is larger?

Since `castSucc` preserves the value and `succ` adds 1, clearly
`castSucc` lands *below* `succ`. Let's prove this.

**Strategy**: Rewrite both sides to values using their val lemmas,
then let `omega` close the arithmetic.

1. `intro i`
2. `rw [Fin.val_castSucc, Fin.val_succ]` — converts to `i.val < i.val + 1`
3. `omega`
"

/-- `castSucc` always lands strictly below `succ`. -/
Statement : ∀ i : Fin 3, i.castSucc.val < i.succ.val := by
  Hint "Start with `intro i`."
  intro i
  Hint "Use `rw [Fin.val_castSucc, Fin.val_succ]` to convert both
  sides to plain natural numbers."
  rw [Fin.val_castSucc, Fin.val_succ]
  Hint "The goal is `i.val < i.val + 1`. `omega` closes this."
  omega

Conclusion "
The **rewrite-to-values** strategy works for comparing any two
`Fin` expressions:
1. Apply val lemmas to simplify `Fin` navigation to ℕ arithmetic
2. Use `omega` to close the resulting goal

This is the standard recipe. It works because the ordering on
`Fin n` is defined through values: `a < b` in `Fin` means
`a.val < b.val` in `ℕ`.

The fact `i.castSucc.val < i.succ.val` means these two functions
never agree — they always land at different positions.
`castSucc` fills positions $0, \\ldots, n-1$; `succ` fills
positions $1, \\ldots, n$. They overlap on $1, \\ldots, n-1$
but at different *input* values.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos
