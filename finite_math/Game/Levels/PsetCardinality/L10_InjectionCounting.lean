import Game.Metadata

World "PsetCardinality"
Level 10

Title "Injection Counting via Equivalence"

Introduction "
# Cross-World Injection Counting

In CountingTypes you counted injections between concrete `Fin` types.
Now combine that with Fintype's equivalence resolution.

Given an abstract type `α` equivalent to `Fin 3`, count the injections
from `α` to `Fin 4`:

$$|\\alpha \\hookrightarrow \\text{Fin}\\;4| = |\\text{Fin}\\;3 \\hookrightarrow \\text{Fin}\\;4| = 4^{\\underline{3}} = 4 \\times 3 \\times 2 = 24$$

This requires the injection-counting formula (from CountingTypes)
combined with equivalence resolution (from Fintype) — a cross-world
combination.
"

/-- Count injections from an abstract type to Fin 4 via equivalence. -/
Statement (α : Type*) [Fintype α] (e : α ≃ Fin 3) :
    Fintype.card (α ↪ Fin 4) = 24 := by
  Hint "Convert to falling factorial, resolve the abstract domain via
  equivalence, evaluate, then unfold. Two worlds combined."
  Hint (hidden := true) "You need (in order): `card_embedding_eq`, `card_congr e`,
  `card_fin` (twice), then `descFactorial_succ` (three times) and `descFactorial_zero`."
  Hint (hidden := true) "Full proof:
  `rw [Fintype.card_embedding_eq, Fintype.card_congr e, Fintype.card_fin, Fintype.card_fin, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`"
  rw [Fintype.card_embedding_eq]
  Hint (hidden := true) "Try `rw [Fintype.card_congr e]` to resolve the abstract domain."
  rw [Fintype.card_congr e]
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "Now unfold the falling factorial: `rw [Nat.descFactorial_succ]` repeatedly, then `rw [Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_succ]
  Hint (hidden := true) "Each `descFactorial_succ` peels off one factor.
  Keep going: `rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_succ,
      Nat.descFactorial_succ, Nat.descFactorial_zero]

Conclusion "
$$|\\alpha \\hookrightarrow \\text{Fin}\\;4| = 4^{\\underline{3}} = 4 \\times 3 \\times 2 = 24$$

This level combined two worlds on a genuinely fresh surface:

| Step | Tool | Source |
|---|---|---|
| 1 | `card_embedding_eq` | CountingTypes |
| 2 | `card_congr e` | Fintype |
| 3-4 | `card_fin` | Fintype |
| 5-8 | `descFactorial_succ/zero` | CountingTypes |

The key move was step 2: the domain `α` is abstract, so you needed
`card_congr` to resolve it before the falling factorial could be
evaluated. In CountingTypes, the domain was always a concrete `Fin k`.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf

-- Force full recursive unfolding
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
