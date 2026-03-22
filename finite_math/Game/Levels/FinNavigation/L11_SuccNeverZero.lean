import Game.Metadata

World "FinNavigation"
Level 11

Title "succ Never Reaches Zero"

Introduction "
# The Dual Separation Fact

In Level 7, you proved that `castSucc` images never equal
`Fin.last` — the **castSucc/last separation**.

Here is the dual: `succ` images never equal `0` — the
**0/succ separation**.

Why? Because `i.succ.val = i.val + 1 >= 1`, but
`(0 : Fin (n+1)).val = 0`. They can't be equal.

The proof uses the same value-reasoning pattern:
1. `intro i h` — assume `h : i.succ = 0`
2. `rw [Fin.ext_iff] at h` — convert to values
3. `rw [Fin.val_succ, Fin.val_zero] at h` — simplify both sides
4. `omega` — `i.val + 1 = 0` is impossible for natural numbers

Notice the new val lemma: **`Fin.val_zero`** says
`(0 : Fin (n+1)).val = 0`. Just as `Fin.val_last` simplifies
`(Fin.last n).val` to `n`, `Fin.val_zero` simplifies `(0).val`
to `0`.
"

/-- No `succ` image equals `0`. -/
Statement : ∀ i : Fin 3, i.succ ≠ (0 : Fin 4) := by
  Hint "The goal is `i.succ ≠ 0`, which means `i.succ = 0 → False`.
  Start with `intro i h`."
  intro i h
  Hint "Convert to values: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify both sides: `rw [Fin.val_succ, Fin.val_zero] at h`.
  `Fin.val_succ` simplifies the left; `Fin.val_zero` simplifies the right."
  rw [Fin.val_succ, Fin.val_zero] at h
  Hint "Now `{h}` says `i.val + 1 = 0`. But `i.val + 1 >= 1 > 0` for
  any natural number. `omega` sees the contradiction."
  omega

Conclusion "
The two separation facts are duals:

| Separation | Statement | Why |
|---|---|---|
| castSucc/last | `j.castSucc ≠ Fin.last n` | `j.val < n` vs `n` |
| 0/succ | `j.succ ≠ 0` | `j.val + 1 >= 1` vs `0` |

Together with their respective decompositions, these give two
**disjoint** partitions of `Fin (n+1)`:

- `Fin (n+1) = image(castSucc) U {last}` (disjointly)
- `Fin (n+1) = {0} U image(succ)` (disjointly)

The proof pattern is identical for both: convert to values, apply
the val lemma, let `omega` see the contradiction.
"

/-- `Fin.val_zero` states that `(0 : Fin (n + 1)).val = 0`.

## Syntax
```
rw [Fin.val_zero]      -- rewrites (0 : Fin n).val to 0
```

## When to use it
When you need to simplify the value of the zero element of `Fin`.
This is the dual of `Fin.val_last`: `val_last` simplifies the
maximum element's value, `val_zero` simplifies the minimum.
-/
TheoremDoc Fin.val_zero as "Fin.val_zero" in "Fin"

NewTheorem Fin.val_zero

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.succ_pos Fin.succ_ne_zero
