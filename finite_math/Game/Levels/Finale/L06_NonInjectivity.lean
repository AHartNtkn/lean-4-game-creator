import Game.Metadata

World "Finale"
Level 6

Title "Non-Injectivity via Image"

Introduction "
# A Second Road to Pigeonhole

Level 5 proved pigeonhole by **fiber decomposition**: decompose
into fibers, bound each fiber, sum the bounds, contradiction.

There's a completely different proof using **image cardinality**.
The key insight: an injective function preserves cardinality,
but the image can't be larger than the codomain.

For $f : \\text{Fin}(n+1) \\to \\text{Fin}\\,n$:
- If $f$ were injective, then $|\\text{image}(f)| = n + 1$
  (by `card_image_of_injective`)
- But $\\text{image}(f) \\subseteq \\text{Fin}\\,n$, so
  $|\\text{image}(f)| \\le n$ (by `subset_univ` + `card_le_card`)
- Contradiction: $n + 1 \\le n$

Prove that $f$ cannot be injective.
"

/-- No function from Fin (n+1) to Fin n is injective. -/
Statement (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ¬ Function.Injective f := by
  Hint "Assume for contradiction that `f` is injective."
  Hint (hidden := true) "Try `intro hinj`."
  intro hinj
  Hint "Use `card_image_of_injective` to compute the image size.
  Since `f` is injective, the image of `Finset.univ` under `f`
  has the same cardinality as the source."
  Hint (hidden := true) "Try
  `have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin (n + 1))) hinj`."
  have himg := Finset.card_image_of_injective
    (Finset.univ : Finset (Fin (n + 1))) hinj
  Hint "Simplify: `Finset.univ.card` for `Fin (n+1)` is `n + 1`."
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin] at himg`."
  rw [Finset.card_univ, Fintype.card_fin] at himg
  Hint "The image lands inside `Finset.univ` of `Fin n`. Use
  `subset_univ` and `card_le_card` to bound the image size."
  Hint (hidden := true) "Try
  `have hsub := Finset.card_le_card (Finset.subset_univ (Finset.univ.image f))`."
  have hsub := Finset.card_le_card
    (Finset.subset_univ (Finset.univ.image f))
  Hint "Simplify: `Finset.univ.card` for `Fin n` is `n`."
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin] at hsub`."
  rw [Finset.card_univ, Fintype.card_fin] at hsub
  Hint "Now `himg` says `image.card = n + 1` and `hsub` says
  `image.card <= n`. Contradiction."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
**Two roads to pigeonhole**:

| Approach | Key tools | Phase |
|----------|-----------|-------|
| Fiber decomposition (L5) | `card_eq_sum_card_fiberwise`, `sum_le_sum` | Phase 7 + 4 |
| Image cardinality (L6) | `card_image_of_injective`, `card_le_card` | Phase 2 + 3 |

Both prove the same underlying fact — that a function from a
larger finite type to a smaller one cannot be injective — but
they use completely different tools.

The **fiber approach** works by decomposing the domain into
fibers and bounding their sizes. The **image approach** works
by comparing the image size to the codomain size.

**Connection to the Cardinality world**: You first saw the
image-based approach in the Cardinality world for specific
small types. Here you proved it for all `n`, confirming
that the technique generalizes.

**When to use which**: The fiber approach gives quantitative
information (which bin is large). The image approach is more
direct when you only need non-injectivity. Both are
fundamental tools in combinatorics.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent library pigeonhole shortcuts
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
