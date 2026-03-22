import Game.Metadata

World "Cardinality"
Level 21

Title "What Does Univ Look Like?"

Introduction "
# Grounding Finset.univ in Concrete Terms

Level 18 introduced `Finset.univ` as the finset of ALL elements of a
finite type. Level 19 showed that everything is a subset of `univ`.
But what does `univ` actually **contain**?

For `Fin 3`, `Finset.univ` should be exactly `{0, 1, 2}` — the three
elements of the type. Let's verify this computationally.

You learned `native_decide` in FinsetImage — it lets Lean compute
both sides of a decidable equality and check they match. Since both
`Finset.univ` and `{0, 1, 2}` are concrete computable finsets, Lean
can verify their equality directly.

**Your task**: Prove that `Finset.univ : Finset (Fin 3)` equals
the literal finset `{0, 1, 2}`.
"

/-- The universal finset of Fin 3 is exactly {0, 1, 2}. -/
Statement : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  Hint "Both sides are concrete, computable finsets. Use `native_decide`
  to let Lean verify the equality computationally."
  Hint (hidden := true) "Try `native_decide`."
  native_decide

Conclusion "
Now you can see what `Finset.univ` actually contains:

$$\\text{Finset.univ} : \\text{Finset}\\;(\\text{Fin}\\;3) = \\{0, 1, 2\\}$$

This is the concrete grounding of the abstract tool: `univ` for `Fin n`
contains exactly the elements $0, 1, \\ldots, n-1$. When Level 18 proved
`(Finset.univ : Finset (Fin 5)).card = 5`, the 5 came from *these*
elements — five specific values, each present exactly once.

The verification used `native_decide` — the same computational tool
from FinsetImage. Both sides are decidably equal, so Lean can check
every element.

This grounding matters for the pigeonhole argument coming next: when
we say 'the image of univ under f,' we mean 'apply f to each of
0, 1, ..., n-1 and collect the results into a finset.'
"

TheoremTab "Card"

-- native_decide intentionally enabled for computational verification
DisabledTactic trivial «decide» simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
