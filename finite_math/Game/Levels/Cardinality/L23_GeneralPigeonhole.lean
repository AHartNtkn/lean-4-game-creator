import Game.Metadata

World "Cardinality"
Level 23

Title "General Pigeonhole"

Introduction "
# Pigeonhole for Any n

Level 21 proved the pigeonhole principle for `Fin 3 -> Fin 2`.
PsetFin's conclusion promised: 'cardinality tools prove pigeonhole
for any n in a few lines.' Time to deliver on that promise.

The proof is **identical** to Level 21 — just replace the specific
numbers with variables:

1. If `f : Fin (n + 2) -> Fin (n + 1)` were injective, the image
   of `univ` would have `n + 2` elements (by `card_image_of_injective`).

2. But the image lives in `Fin (n + 1)`, so it has at most `n + 1`
   elements (by `card_le_card` + `subset_univ`).

3. So `n + 2 <= n + 1` — contradiction.

**Your task**: Prove the general pigeonhole principle for all `n`.
"

/-- No injective function from Fin (n+2) to Fin (n+1) exists, for any n. -/
Statement (n : ℕ) (f : Fin (n + 2) → Fin (n + 1)) : ¬ Function.Injective f := by
  Hint "The proof has exactly the same structure as Level 21.
  Start by assuming `f` is injective: `intro hinj`."
  intro hinj
  Hint "Use `card_image_of_injective` to compute the image size.
  Then simplify with `card_univ` and `card_fin`."
  Hint (hidden := true) "`have h1 := Finset.card_image_of_injective (Finset.univ : Finset (Fin (n + 2))) hinj`
  `rw [Finset.card_univ, Fintype.card_fin] at h1`"
  have h1 := Finset.card_image_of_injective (Finset.univ : Finset (Fin (n + 2))) hinj
  rw [Finset.card_univ, Fintype.card_fin] at h1
  Hint "Now bound the image size using `card_le_card` and `subset_univ`."
  Hint (hidden := true) "`have h2 := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset (Fin (n + 2))).image f))`
  `rw [Finset.card_univ, Fintype.card_fin] at h2`"
  have h2 := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset (Fin (n + 2))).image f))
  rw [Finset.card_univ, Fintype.card_fin] at h2
  Hint "`h1` says the image has `n + 2` elements, `h2` says it has
  at most `n + 1`. `omega` sees the contradiction."
  omega

Conclusion "
The **general pigeonhole principle**: for ANY `n`, no injective
function from `Fin (n + 2)` to `Fin (n + 1)` exists.

The proof was *identical* to Level 21 — the same three steps,
the same lemmas. The numbers changed from `3` and `2` to `n + 2`
and `n + 1`, but `omega` handles the arithmetic in both cases.

This is the power of the cardinality approach: the proof doesn't
depend on the specific sizes. The PsetFin approach (exhaustive
case analysis) only worked for specific values — extending it to
`Fin 100 -> Fin 99` would require checking 100! combinations.
The counting argument handles all sizes in four lines.

**The pigeonhole principle in plain language**: if you put $n + 2$
pigeons into $n + 1$ holes, at least two pigeons must share a hole.
The counting argument: if each hole had at most one pigeon
(injectivity), you'd need at least $n + 2$ holes, but only $n + 1$
exist.

**Connection to card_image_le**: The pigeonhole principle is really a
corollary of a fact you already know: `Finset.card_le_card`
applied to `image f univ \\subseteq univ`. If $f$ were injective,
`card_image_of_injective` would give
$|\\text{image}| = n + 2$, but the image lives in `Fin (n + 1)` so
$|\\text{image}| \\le n + 1$ by `card_le_card` + `subset_univ`.
Contradiction. In other words, **pigeonhole IS the statement that
non-injective maps shrink image cardinality** — which is exactly
what `card_image_le` bounds.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.card_le_of_injective Finset.card_le_univ Finset.eq_univ_of_card
