import GameServer.Commands
import Mathlib

World "Capstone"
Level 3

Title "Sum over Fintype.univ"

Introduction
"
# Summing a constant over `Fintype.univ`

A fundamental connection between counting and big operators: summing a
constant `c` over all elements of a finite type gives `card * c`.

## The chain of reasoning

```
∑ _ : Fin n, c = (Finset.univ : Finset (Fin n)).card • c     -- Finset.sum_const
                = Fintype.card (Fin n) • c                     -- Finset.card_univ
                = n • c                                        -- Fintype.card_fin
                = n * c                                        -- smul_eq_mul
```

## Your task

Prove that `∑ _ : Fin 5, (3 : ℕ) = 15`.

This is `5 * 3 = 15`, but you need to derive it from the big-operator
API rather than computing directly.
"

/-- Summing the constant 3 over `Fin 5` gives 15. -/
Statement : ∑ _ : Fin 5, (3 : ℕ) = 15 := by
  Hint "Start with `rw [Finset.sum_const]` to convert the sum of a
  constant into `card • 3`."
  Hint (hidden := true) "Try `rw [Finset.sum_const]`."
  rw [Finset.sum_const]
  Hint "Good! The goal is now `Finset.univ.card • 3 = 15`.

  Use `rw [Finset.card_univ]` to replace `Finset.univ.card` with
  `Fintype.card (Fin 5)`."
  Hint (hidden := true) "Try `rw [Finset.card_univ]`."
  rw [Finset.card_univ]
  Hint "Now use `rw [Fintype.card_fin]` to get `5 • 3 = 15`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin]`."
  rw [Fintype.card_fin]
  Hint "The goal is `5 • 3 = 15`. Convert scalar multiplication to
  ordinary multiplication with `rw [smul_eq_mul]`, then close with `norm_num`."
  Hint (hidden := true) "Try `rw [smul_eq_mul]` then `norm_num`."
  rw [smul_eq_mul]

Conclusion
"
You proved that summing a constant over a finite type reduces to
multiplication by the cardinality. The proof chain is:

1. `sum_const` — converts a constant sum to `card • c`
2. `card_univ` — connects finset cardinality to `Fintype.card`
3. `card_fin` — evaluates `Fintype.card (Fin n) = n`
4. `smul_eq_mul` — converts `n • c` to `n * c`

## In ordinary mathematics

This is the trivial identity $\\sum_{i=1}^{n} c = nc$. The Lean proof
makes explicit what paper mathematics takes for granted: the
connection between 'how many terms' (cardinality) and 'what each term
contributes' (the constant).
"

DisabledTactic trivial decide native_decide simp aesop simp_all
