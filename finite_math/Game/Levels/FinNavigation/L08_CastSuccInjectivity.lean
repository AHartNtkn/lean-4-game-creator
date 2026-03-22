import Game.Metadata

World "FinNavigation"
Level 8

Title "castSucc is Injective"

Introduction "
# castSucc Preserves Distinctness

In Level 7, you proved that `castSucc` images are disjoint from
`Fin.last`. But there's another important property: `castSucc` is
**injective** — it never sends two different elements to the same
place.

Why? Because `castSucc` preserves values. If
`i.castSucc = j.castSucc`, then their values are equal
(`i.castSucc.val = j.castSucc.val`), and since `castSucc` preserves
values (`val_castSucc`), we get `i.val = j.val`, so `i = j`.

This matters because the decomposition (which you'll prove in the
boss) depends on `castSucc` being a genuine embedding — mapping
`Fin n` *injectively* into `Fin (n+1)`. If `castSucc` could collapse
two elements, the decomposition would be wrong.

**Strategy**: The pattern is the same as succ injectivity:
1. `intro i j h`
2. `rw [Fin.ext_iff] at h` — convert equality to values
3. `rw [Fin.val_castSucc, Fin.val_castSucc] at h` — simplify
4. `ext` — reduce the goal to values
5. `exact h` — close with the hypothesis
"

/-- `castSucc` is injective: equal outputs imply equal inputs. -/
Statement : ∀ i j : Fin 3, i.castSucc = j.castSucc → i = j := by
  Hint "Start with `intro i j h`."
  intro i j h
  Hint "Convert `{h}` to a value equality: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify the `castSucc` values:
  `rw [Fin.val_castSucc, Fin.val_castSucc] at h`.
  This gives `{h}` as `i.val = j.val`."
  rw [Fin.val_castSucc, Fin.val_castSucc] at h
  Hint "Now reduce the goal to values with `ext`, then close with
  `exact h`."
  ext
  exact h

Conclusion "
The **injectivity pattern** for `Fin` functions:
```
rw [Fin.ext_iff] at h
rw [val_lemma, val_lemma] at h
ext
exact h  -- or omega
```

Convert the hypothesis to values, simplify with val lemmas, then
transfer to the goal. This is exactly the same pattern you'll use
in Level 9 for `succ` injectivity — the only difference is which
val lemma you use (`val_castSucc` vs `val_succ`).

Both `castSucc` and `succ` are injective — you've just proved it
for `castSucc`, and you'll prove it for `succ` next. Together with
the separation fact (Level 7), this tells you: `castSucc` is a
*perfect copy* of `Fin n` inside `Fin (n+1)`, preserving both
values and distinctness.

This property — **equal outputs imply equal inputs** — is called
**injectivity**. In Lean, `Function.Injective f` means
`∀ a b, f a = f b → a = b`. You'll meet this formal definition
in the FinsetImage world, where injectivity controls whether
image preserves cardinality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_inj
