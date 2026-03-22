import Game.Metadata

World "CountingTypes"
Level 10

Title "The Gap: Non-Injective Functions"

Introduction "
# How Many Non-Injective Functions?

Every injection `Fin k ↪ Fin n` is also a function `Fin k → Fin n`,
but not every function is an injection. The **gap** between the two
counts tells you how many functions 'waste' a slot by mapping two
inputs to the same output:

$$\\text{non-injective} = n^k - n^{\\underline{k}}$$

For `k = 2` and `n = 5`: there are $5^2 = 25$ functions and
$5^{\\underline{2}} = 5 \\times 4 = 20$ injections. So exactly
$25 - 20 = 5$ functions are non-injective.

Which 5? They are the functions that send both inputs to the same
output: `(0,0), (1,1), (2,2), (3,3), (4,4)` — exactly the diagonal.

**Your task**: Prove this formally. You'll compute each count in a
`have` block, then let `omega` find the difference. This is a
rehearsal for the boss, which uses the same dual-computation strategy
on a harder type.
"

/-- There are 5 non-injective functions from Fin 2 to Fin 5. -/
Statement : Fintype.card (Fin 2 → Fin 5) - Fintype.card (Fin 2 ↪ Fin 5) = 5 := by
  Hint "This is a subtraction — you need the value of both terms.
  Start by computing the function count in a `have` block."
  Hint (hidden := true) "Enter:
  `have hfun : Fintype.card (Fin 2 → Fin 5) = 25 := by`
  then prove it inside the `by` block."
  have hfun : Fintype.card (Fin 2 → Fin 5) = 25 := by
    Hint "Decompose the function type, then evaluate the base types."
    Hint (hidden := true) "Try `rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]`
    then `omega`."
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    Hint "Close the arithmetic with `omega`."
    omega
  Hint "Good — 25 functions. Now compute the injection count."
  Hint (hidden := true) "Enter:
  `have hinj : Fintype.card (Fin 2 ↪ Fin 5) = 20 := by`"
  have hinj : Fintype.card (Fin 2 ↪ Fin 5) = 20 := by
    Hint "Convert to a falling factorial, evaluate base types, then unfold."
    Hint (hidden := true) "Try
    `rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]`
    then unfold the falling factorial."
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    Hint "Unfold `5.descFactorial 2` — two `descFactorial_succ` plus
    `descFactorial_zero`."
    Hint (hidden := true) "Try
    `rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`."
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
  Hint "You have both counts. Let `omega` compute the difference."
  omega

Conclusion "
$$25 - 20 = 5 \\text{ non-injective functions}$$

The 5 non-injective functions `Fin 2 → Fin 5` are exactly the
**constant-on-both-inputs** functions: those sending both `0` and `1`
to the same target. With 5 possible targets, there are 5 such
functions.

**The dual-computation strategy**:
1. Compute the total count in a `have` block
2. Compute the restricted count in another `have` block
3. Close with `omega`

The boss uses this exact strategy on a harder type — with an abstract
domain requiring `card_congr` and a composite codomain requiring
`card_sum`.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Force full recursive unfolding
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
