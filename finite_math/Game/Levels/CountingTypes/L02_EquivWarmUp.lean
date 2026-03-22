import Game.Metadata

World "CountingTypes"
Level 2

Title "Counting via Equivalence"

Introduction "
# Functions on an Equivalent Type

Sometimes the domain of a function type is abstract — you know it's
equivalent to a concrete type, but it isn't literally `Fin n` or `Bool`.

Suppose `α` is a type with `e : α ≃ Bool`. Then `α` has the same
number of elements as `Bool`, so functions `α → Fin 3` should number
the same as functions `Bool → Fin 3`, which is $3^2 = 9$.

The key step is `Fintype.card_congr`: given `e : α ≃ Bool`, the
rewrite `rw [Fintype.card_congr e]` replaces `Fintype.card α` with
`Fintype.card Bool` in the goal.

**Your task**: Prove that there are 9 functions from `α` to `Fin 3`,
using the equivalence `e` to resolve the abstract domain.
"

/-- There are 9 functions from a two-element type to Fin 3. -/
Statement (α : Type*) [DecidableEq α] [Fintype α] (e : α ≃ Bool) :
    Fintype.card (α → Fin 3) = 9 := by
  Hint "Start with `rw [Fintype.card_fun]` to decompose the function type."
  rw [Fintype.card_fun]
  Hint "The exponent is `Fintype.card α`, but `α` is abstract. Use the
  equivalence: `rw [Fintype.card_congr e]` replaces `Fintype.card α`
  with `Fintype.card Bool`."
  Hint (hidden := true) "Try `rw [Fintype.card_congr e]`."
  rw [Fintype.card_congr e]
  Hint "Now evaluate the base types and close the arithmetic."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_bool]`
  then `omega`."
  rw [Fintype.card_fin, Fintype.card_bool]
  omega

Conclusion "
$$|\\alpha \\to \\text{Fin}\\;3| = 3^{|\\alpha|} = 3^{|\\text{Bool}|} = 3^2 = 9$$

The key move was `rw [Fintype.card_congr e]`: when the domain (or
codomain) is abstract, an equivalence lets you swap it for a concrete
type whose cardinality you know.

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_fun` | split into base ^ exponent |
| 2 | `card_congr e` | resolve abstract domain to `Bool` |
| 3 | `card_fin`, `card_bool` | evaluate base types |
| 4 | `omega` | close the arithmetic |

This pattern — using `card_congr` mid-computation — will return in the
boss level, where the domain requires an equivalence to decompose.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
