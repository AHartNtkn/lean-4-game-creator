import Game.Metadata

World "PsetFin"
Level 2

Title "CastSucc Never Reaches Last"

Introduction "
# Abstract Navigation

In FinNavigation, you proved that `castSucc` images are strictly
below `last` for specific small types like `Fin 3`. Here you'll
prove the same fact **for all `n`**.

The proof strategy is the same as the concrete case:
1. Assume equality
2. Convert to values with `Fin.ext_iff`
3. Apply val lemmas
4. Derive a contradiction with `omega`

But now `n` is a variable, not a concrete number. The proof works
identically — `omega` handles the abstract arithmetic.
"

/-- No `castSucc` image equals `Fin.last`. -/
Statement (n : ℕ) (i : Fin (n + 1)) :
    i.castSucc ≠ Fin.last (n + 1) := by
  Hint "The goal is `a ≠ b`, which means `a = b → False`.
  Start with `intro h` to assume they're equal."
  intro h
  Hint "Now convert the Fin equality to a value equality.
  Use `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Apply the val lemmas to simplify:
  `rw [Fin.val_castSucc, Fin.val_last] at h`."
  Hint (hidden := true) "After the rewrites, `h` says `i.val = n + 1`.
  But `i : Fin (n + 1)` means `i.val < n + 1`. Contradiction!
  `omega` sees both facts and closes the goal."
  rw [Fin.val_castSucc, Fin.val_last] at h
  omega

Conclusion "
The same proof pattern from FinNavigation — convert to values,
apply val lemmas, use `omega` — works for abstract `n`, not just
concrete types like `Fin 3`.

This is an important transfer: the concrete proofs you practiced
in FinNavigation are templates for general proofs. The structure
is identical; only the numbers change to variables.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Fin.castSucc_lt_last Fin.castSucc_ne_last
