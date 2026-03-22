import Game.Metadata

World "CountingTypes"
Level 9

Title "Injections into a Sum Type"

Introduction "
# Injections into a Composite Codomain

In the last level you counted injections from `Fin k` to `Fin n` —
both simple `Fin` types. But what if the codomain is built from
smaller types?

Here the codomain is `Bool ⊕ Fin 4` — a sum type with
$|\\text{Bool}| + |\\text{Fin}\\;4| = 2 + 4 = 6$ elements. The domain
is `Fin 3` with 3 elements.

You need to:
1. Apply `card_embedding_eq` to convert to a falling factorial
2. Resolve the codomain with `card_sum`, `card_bool`, `card_fin`
3. Resolve the domain with `card_fin`
4. Unfold the falling factorial

This combines `card_embedding_eq` with `card_sum` — a new
combination that will return in the boss.
"

/-- There are 120 injections from Fin 3 to Bool ⊕ Fin 4. -/
Statement : Fintype.card (Fin 3 ↪ (Bool ⊕ Fin 4)) = 120 := by
  Hint "Start with `rw [Fintype.card_embedding_eq]` to convert to a
  falling factorial."
  rw [Fintype.card_embedding_eq]
  Hint "Now resolve all the type cardinalities. The codomain is
  `Bool ⊕ Fin 4` (use `card_sum`, `card_bool`, `card_fin`), and the
  domain is `Fin 3` (use `card_fin`)."
  Hint (hidden := true) "Try
  `rw [Fintype.card_sum, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_sum, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
  Hint "The goal is `6.descFactorial 3 = 120`. Unfold the falling
  factorial: three `descFactorial_succ` rewrites plus
  `descFactorial_zero`."
  Hint (hidden := true) "Try
  `rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
      Nat.descFactorial_succ, Nat.descFactorial_zero]

Conclusion "
$$|\\text{Fin}\\;3 \\hookrightarrow (\\text{Bool} \\oplus \\text{Fin}\\;4)| = 6^{\\underline{3}} = 6 \\times 5 \\times 4 = 120$$

This time the codomain was a **sum type**, so you needed `card_sum`
to resolve it before the falling factorial computation:

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_embedding_eq` | convert to falling factorial |
| 2 | `card_sum`, `card_bool`, `card_fin` | resolve codomain to 6 |
| 3 | `card_fin` | resolve domain to 3 |
| 4 | `descFactorial_succ/zero` | unfold $6^{\\underline{3}}$ |

**Pattern**: when counting injections into a composite codomain,
first convert to a falling factorial, then decompose the codomain
to get its total size, resolve the domain, and unfold. The boss will
use this exact pattern with both `card_sum` and `card_prod` in the
domain and codomain.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Force full recursive unfolding
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
