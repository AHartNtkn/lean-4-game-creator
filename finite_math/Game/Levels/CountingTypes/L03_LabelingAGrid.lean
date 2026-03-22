import Game.Metadata

World "CountingTypes"
Level 3

Title "Labeling a Grid"

Introduction "
# Labeling Cells of a Grid

Imagine an `m`-by-`n` grid of cells. Each cell can be labeled `true`
or `false`. How many labelings exist?

The grid is `Fin m × Fin n` (`m` rows, `n` columns). A labeling is a
function from the grid to `Bool`:

$$|\\text{Fin}\\;m \\times \\text{Fin}\\;n \\to \\text{Bool}| = 2^{m \\cdot n}$$

For example, a 2-by-3 grid has $2^{2 \\cdot 3} = 2^6 = 64$ labelings.

The proof requires a **multi-step decomposition**: first `card_fun`
to handle the function type, then `card_bool` for the codomain, then
`card_prod` to decompose the product domain, then `card_fin` for each
factor.

**Your task**: Prove this for general `m` and `n`.
"

/-- There are 2^(m*n) ways to label an m-by-n grid with true/false. -/
Statement (m n : ℕ) : Fintype.card (Fin m × Fin n → Bool) = 2 ^ (m * n) := by
  Hint "The outer structure is a function type. Decompose it first —
  always handle the outermost type constructor before working inward."
  Hint (hidden := true) "Try `rw [Fintype.card_fun]`."
  rw [Fintype.card_fun]
  Hint "The codomain `Bool` has a known cardinality. Evaluate it."
  Hint (hidden := true) "Try `rw [Fintype.card_bool]`."
  rw [Fintype.card_bool]
  Hint "The domain is a product type. What rule decomposes product
  cardinality into a multiplication?"
  Hint (hidden := true) "Try `rw [Fintype.card_prod]`."
  rw [Fintype.card_prod]
  Hint "Evaluate the remaining `Fin` types to get concrete numbers."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_fin, Fintype.card_fin]

Conclusion "
$$|\\text{Fin}\\;m \\times \\text{Fin}\\;n \\to \\text{Bool}| = 2^{m \\cdot n}$$

This was your first **multi-step decomposition**: the function type
needed `card_fun`, the codomain needed `card_bool`, the domain product
needed `card_prod`, and each factor needed `card_fin`.

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_fun` | split into base and exponent |
| 2 | `card_bool` | evaluate codomain to 2 |
| 3 | `card_prod` | decompose domain product |
| 4 | `card_fin` (x2) | evaluate domain factors |

**Strategy tip**: always decompose the outermost type constructor first
(function), then work inward (product in the domain, base types last).
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
