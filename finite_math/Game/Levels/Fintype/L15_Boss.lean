import Game.Metadata

World "Fintype"
Level 15

Title "Boss: Composite Cardinality"

Introduction "
# Boss: How Many Functions?

Time to put everything together. You have seven card_* lemmas:

| Lemma | What it decomposes |
|---|---|
| `Fintype.card_fin` | `card (Fin n) = n` |
| `Fintype.card_bool` | `card Bool = 2` |
| `Fintype.card_prod` | `card (α × β) = card α * card β` |
| `Fintype.card_sum` | `card (α ⊕ β) = card α + card β` |
| `Fintype.card_fun` | `card (α → β) = card β ^ card α` |
| `Fintype.card_congr e` | `α ≃ β → card α = card β` |
| `Fintype.card_subtype_compl` | `card {x // ¬P x} = card α - card P` |

**Your task**: Given an abstract type `α ≃ Fin 2 × Bool` and a
predicate `P` with `card P = 1`, compute the number of functions
from `{x : α // ¬P x}` to `Fin 2 ⊕ Fin 3`.

Think about it mathematically first:
- `α ≃ Fin 2 × Bool`, so `card α = 2 * 2 = 4`
- `card P = 1`, so `card {x // ¬P x} = 4 - 1 = 3`
- The codomain `Fin 2 ⊕ Fin 3` has `2 + 3 = 5` elements
- The number of functions is `5 ^ 3 = 125`

The `[DecidableEq α]` constraint is a technical requirement that lets
Lean compare elements of `α` for equality — it's needed when counting
functions on abstract types, similar to how `[Fintype α]` is needed
for `Fintype.card`. You won't need to interact with it directly.

You'll need ALL seven lemmas (plus `omega` for the final arithmetic).
"

/-- The number of functions from {x : α // ¬P x} to Fin 2 ⊕ Fin 3 is 125,
    given that α ≃ Fin 2 × Bool and card P = 1. -/
Statement (α : Type*) [DecidableEq α] [Fintype α] (e : α ≃ Fin 2 × Bool)
    (P : α → Prop) [DecidablePred P] [Fintype {x // P x}] [Fintype {x // ¬P x}]
    (hp : Fintype.card {x // P x} = 1) :
    Fintype.card ({x : α // ¬P x} → Fin 2 ⊕ Fin 3) = 125 := by
  Hint "Start by decomposing the function type with `rw [Fintype.card_fun]`."
  rw [Fintype.card_fun]
  Hint "The domain is a complement subtype. Apply complement counting:
  `rw [Fintype.card_subtype_compl]`."
  rw [Fintype.card_subtype_compl]
  Hint "Now use the equivalence `e` to resolve `Fintype.card α`.
  Try `rw [Fintype.card_congr e]`."
  rw [Fintype.card_congr e]
  Hint "Decompose the domain with `rw [Fintype.card_prod]` and the
  codomain with `rw [Fintype.card_sum]`."
  rw [Fintype.card_prod, Fintype.card_sum]
  Hint "Evaluate the individual type cardinalities with `card_fin`,
  `card_bool`, and the hypothesis `hp`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, hp]`.
  (Note: `card_fin` replaces all occurrences of `Fin 2` at once, so
  two `card_fin` calls handle all three `Fin` types.)"
  rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, hp]
  Hint "The goal is now `(2 + 3) ^ (2 * 2 - 1) = 125`, i.e., `5 ^ 3 = 125`.
  Use `omega` for the arithmetic."
  omega

Conclusion "
You computed the cardinality of a composite function type using ALL
seven card_* lemmas:

$$|\\{x : \\alpha \\mid \\neg P\\,x\\} \\to \\text{Fin}\\;2 \\oplus \\text{Fin}\\;3| = 5^3 = 125$$

The proof decomposed from the outside in:

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_fun` | split into `card (Fin 2 ⊕ Fin 3) ^ card {x // ¬P x}` |
| 2 | `card_subtype_compl` | resolve domain to `card α - card P` |
| 3 | `card_congr e` | resolve `card α` to `card (Fin 2 × Bool)` |
| 4 | `card_prod` | decompose `card (Fin 2) * card Bool` |
| 5 | `card_sum` | decompose codomain `card (Fin 2) + card (Fin 3)` |
| 6 | `card_fin` (×2), `card_bool`, `hp` | evaluate to `(2 + 3) ^ (2 * 2 - 1)` |
| 7 | `omega` | `5 ^ 3 = 125` |

## Your Fintype Toolkit

| Lemma | Formula |
|---|---|
| `card_fin n` | `card (Fin n) = n` |
| `card_bool` | `card Bool = 2` |
| `card_prod` | `card (α × β) = card α * card β` |
| `card_sum` | `card (α ⊕ β) = card α + card β` |
| `card_fun` | `card (α → β) = card β ^ card α` |
| `card_congr e` | `α ≃ β → card α = card β` |
| `card_subtype_compl` | `card {x // ¬P x} = card α - card P` |

These seven lemmas can compute the cardinality of any type built from
finite building blocks using products, sums, function types,
equivalences, and subtypes.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
