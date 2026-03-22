import Game.Metadata

World "Cardinality"
Level 22

Title "Abstract Pigeonhole via Cardinality"

Introduction "
# Pigeonhole Without Case Analysis

In PsetFin, you proved the pigeonhole principle for `Fin 3 -> Fin 2`
by exhaustive case analysis — 6 branches, each checked by hand.
The conclusion promised: 'cardinality tools prove pigeonhole for
any n in a few lines.' Time to deliver.

The cardinality argument is beautifully simple:

1. If `f : Fin 3 -> Fin 2` were injective, then by
   `card_image_of_injective`, the image of ALL `Fin 3` elements
   under `f` would have `3` elements.

2. But the image lives inside `Fin 2`, which only has `2` elements.
   By `card_le_card` + `subset_univ`, the image has
   at most `2` elements.

3. So `3 <= 2` — contradiction.

No case analysis. No classifying outputs. Just counting.

All three tools were introduced in the previous two levels:
`Finset.univ`, `card_univ`, `card_fin`, and `subset_univ`. Now you
combine them with `card_image_of_injective` and `card_le_card` for
the full pigeonhole argument.
"

/-- No injective function from Fin 3 to Fin 2 exists. -/
Statement (f : Fin 3 → Fin 2) : ¬ Function.Injective f := by
  Hint "Assume for contradiction that `f` is injective.
  Use `intro hinj`."
  intro hinj
  Hint "Use `card_image_of_injective` to get the size of the image.
  `have h1 := Finset.card_image_of_injective (Finset.univ : Finset (Fin 3)) hinj`
  gives: `(Finset.univ.image f).card = Finset.univ.card`."
  Hint (hidden := true) "Then use `Finset.card_univ` and `Fintype.card_fin`
  to simplify: `rw [Finset.card_univ, Fintype.card_fin] at h1`.
  This gives `(univ.image f).card = 3`."
  have h1 := Finset.card_image_of_injective (Finset.univ : Finset (Fin 3)) hinj
  rw [Finset.card_univ, Fintype.card_fin] at h1
  Hint "Now bound the image size. The image `univ.image f` is a
  subset of `univ : Finset (Fin 2)` (everything lives in the target).
  Use `card_le_card` with `subset_univ`."
  Hint (hidden := true) "`have h2 := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset (Fin 3)).image f))`
  `rw [Finset.card_univ, Fintype.card_fin] at h2`
  gives `(univ.image f).card <= 2`."
  have h2 := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset (Fin 3)).image f))
  rw [Finset.card_univ, Fintype.card_fin] at h2
  Hint "Now `h1` says the image has 3 elements, `h2` says it
  has at most 2. `omega` sees the contradiction."
  omega

Conclusion "
The entire proof in 4 lines:
1. `card_image_of_injective` + injectivity gives image size = source size = 3
2. `card_le_card` + `subset_univ` gives image size <= target size = 2
3. `omega`: 3 <= 2 is false

Compare this to the PsetFin proof: 99 lines of case analysis
with 6 branches. The cardinality argument works for ANY `n`:
no injective function from `Fin (n+2)` to `Fin (n+1)` exists,
because the image would need `n+2` elements but the target only
has `n+1`. No enumeration, no branches — just arithmetic.

This is the **abstract pigeonhole principle**: more pigeons than
holes forces a collision. The counting argument replaces
case-by-case checking with a single size comparison.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.card_le_of_injective Finset.card_le_univ Finset.eq_univ_of_card
