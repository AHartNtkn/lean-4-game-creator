import Game.Metadata

World "FinNavigation"
Level 7

Title "castSucc Never Reaches Last"

Introduction "
# The Key Structural Fact

Here is the most important fact about `Fin` navigation:

> `castSucc` and `Fin.last` produce **disjoint** elements.

No element in the image of `castSucc` can equal `Fin.last n`.
Why? Because `castSucc` preserves values in $\\{0, \\ldots, n-1\\}$,
while `Fin.last n` has value $n$.

To prove `j.castSucc ≠ Fin.last 3`, you need to show that
assuming they are equal leads to a contradiction. The strategy:

1. `intro j h` — assume `h : j.castSucc = Fin.last 3`
2. `rw [Fin.ext_iff] at h` — convert to `j.castSucc.val = (Fin.last 3).val`
3. `rw [Fin.val_castSucc, Fin.val_last] at h` — simplify to `j.val = 3`
4. `omega` — contradicts `j.val < 3` (since `j : Fin 3`)

This is the **value reasoning** pattern: convert `Fin` facts to
value facts, then let arithmetic close the gap.
"

/-- No `castSucc` image equals `Fin.last`. -/
Statement : ∀ j : Fin 3, j.castSucc ≠ Fin.last 3 := by
  Hint "Start with `intro j h` to assume equality for contradiction."
  intro j h
  Hint "Convert to values: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify: `rw [Fin.val_castSucc, Fin.val_last] at h`.
  This gives `h : j.val = 3`."
  rw [Fin.val_castSucc, Fin.val_last] at h
  Hint "Now `{h}` says `j.val = 3`, but `j : Fin 3` means
  `j.val < 3`. `omega` sees the contradiction."
  omega

Conclusion "
This is the **separation fact**: the images of `castSucc`
(values $0, \\ldots, n-1$) and `Fin.last` (value $n$) don't overlap.

Together with the *maximum fact* from Level 2, this tells you:
`Fin (n+1)` splits into two disjoint parts:
- Elements with value $< n$ (the `castSucc` images)
- The single element with value $= n$ (`Fin.last n`)

This decomposition is like the natural number fact that every
$k \\leq n$ either satisfies $k < n$ or $k = n$.

The proof pattern — `ext_iff`, then val lemmas, then `omega` —
is how you reason about `Fin` equality and inequality at the
value level. You'll use it again in the boss.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_ne_last Fin.castSucc_lt_last
