import Game.Metadata

World "FinNavigation"
Level 9

Title "succ is Injective"

Introduction "
# succ Preserves Distinctness

In Level 8, you proved that `castSucc` is injective. The same is
true for `succ`: if `i.succ = j.succ`, then `i = j`.

Why? Because `succ` adds 1 to the value. If
`i.succ.val = j.succ.val`, then `i.val + 1 = j.val + 1`, so
`i.val = j.val`, so `i = j`.

The proof pattern is identical to Level 8 — just swap
`val_castSucc` for `val_succ`:
1. `intro i j h`
2. `rw [Fin.ext_iff] at h` — convert equality to values
3. `rw [Fin.val_succ, Fin.val_succ] at h` — simplify
4. `ext` — reduce the goal to values
5. `omega` — close with the simplified hypothesis
"

/-- `succ` is injective: equal outputs imply equal inputs. -/
Statement : ∀ i j : Fin 3, i.succ = j.succ → i = j := by
  Hint "Start with `intro i j h`."
  intro i j h
  Hint "Convert `{h}` to a value equality: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify the `succ` values:
  `rw [Fin.val_succ, Fin.val_succ] at h`.
  This gives `i.val + 1 = j.val + 1`."
  rw [Fin.val_succ, Fin.val_succ] at h
  Hint "Now reduce the goal to values with `ext`, then close with
  `omega`."
  ext
  omega

Conclusion "
The injectivity pattern works the same for both navigation functions:

| Function | Convert hypothesis | Simplify | Close |
|---|---|---|---|
| `castSucc` | `rw [Fin.ext_iff] at h` | `rw [val_castSucc, val_castSucc] at h` | `ext; exact h` |
| `succ` | `rw [Fin.ext_iff] at h` | `rw [val_succ, val_succ] at h` | `ext; omega` |

The only difference: after simplifying `succ` values, `h` says
`i.val + 1 = j.val + 1` instead of `i.val = j.val`, so you need
`omega` instead of `exact h` to cancel the `+ 1`.

Both `castSucc` and `succ` are injective — each gives a *faithful*
copy of `Fin n` inside `Fin (n+1)`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.succ_inj
