import Game.Metadata

World "FinNavigation"
Level 6

Title "castSucc and succ Never Agree"

Introduction "
# Different Embeddings, Different Outputs

In Level 5, you proved that `i.castSucc.val < i.succ.val` — the
value of `castSucc` is strictly less than the value of `succ`.
The immediate consequence: **they can never be equal**.

If `i.castSucc = i.succ`, then their values would be equal. But
you just showed one is strictly less than the other. Contradiction.

The proof uses the same value-reasoning pattern you've been
practicing:
1. `intro i h` — assume `h : i.castSucc = i.succ`
2. `rw [Fin.ext_iff] at h` — convert to values
3. `rw [Fin.val_castSucc, Fin.val_succ] at h` — simplify
4. `omega` — `i.val = i.val + 1` is impossible

This is a direct corollary of Level 5's strict inequality.
"

/-- `castSucc` and `succ` never produce the same output. -/
Statement : ∀ i : Fin 3, i.castSucc ≠ i.succ := by
  Hint "Start with `intro i h` to assume they're equal."
  intro i h
  Hint "Convert to values: `rw [Fin.ext_iff] at h`."
  rw [Fin.ext_iff] at h
  Hint "Simplify both sides: `rw [Fin.val_castSucc, Fin.val_succ] at h`."
  rw [Fin.val_castSucc, Fin.val_succ] at h
  Hint "Now the hypothesis says `i.val = i.val + 1`. This is impossible
  for natural numbers. `omega` closes the goal."
  omega

Conclusion "
This completes the picture of how `castSucc` and `succ` relate:

| Fact | Statement | Proved in |
|---|---|---|
| Value ordering | `i.castSucc.val < i.succ.val` | Level 5 |
| Disjointness | `i.castSucc /= i.succ` | This level |

The two embedding functions `castSucc` and `succ` have **disjoint
images at each input** — for any given `i`, the element `castSucc`
lands on is always different from where `succ` lands.

This proof used a pattern that deserves a name: the **value
reduction strategy for hypotheses**. When you have a hypothesis
`h` about `Fin` elements:
1. `rw [Fin.ext_iff] at h` — reduce to values
2. `rw [val_lemma, ...] at h` — simplify to ℕ arithmetic
3. `omega` — derive a contradiction or close the goal

In Level 5, you used the goal-level version (rewrite the *goal*
to values, then `omega`). Here you used the hypothesis-level
version (rewrite the *hypothesis* to values, then `omega`). Both
are instances of the same idea: **reduce Fin reasoning to ℕ
arithmetic, then let omega handle it**.

Combined with the separation facts (next levels) and the
decompositions (later), this means `Fin (n+1)` is neatly
partitioned by these two embedding functions.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos
