import Game.Metadata

World "CountingTechniques"
Level 16

Title "The Averaging Argument"

Introduction "
# Pigeonhole from Fiber Decomposition

You've learned pigeonhole (Level 8) and fiber decomposition
(Level 11) as separate techniques. Now we connect them.

**The averaging argument**: If you distribute `n + 1` items
among `n` bins, some bin must contain at least 2 items.
This is pigeonhole — but instead of using `not_injective_of_card_lt`
directly, we prove it from fiber decomposition:

1. Assume for contradiction that every fiber has size at most 1
2. The fiber sum equals the source size: `sum fiber_sizes = n + 1`
3. By `sum_le_sum` (Level 13), the sum is at most `n * 1 = n`
4. But `n + 1 > n`, contradiction — so some fiber has size >= 2

This shows that **pigeonhole is a consequence of double counting**.

**About `by_contra`**: You'll start this proof with `by_contra`,
which assumes the negation of the goal and changes the target to
`False`. You've seen this pattern before (from the FinsetOperations
world) — assume what you want to disprove, then derive a
contradiction.

**The `hmem` step**: To apply `card_eq_sum_card_fiberwise`, you need
a proof that every element maps into the target set. For `Finset.univ`,
the proof is `fun _ _ => Finset.mem_univ _` — this is an anonymous
function that takes any element and any membership proof, and returns
`Finset.mem_univ _` (the fact that every element is in `univ`).
The underscores let Lean infer the specific element.

**Your task**: Prove that some fiber of `f : Fin (n+1) -> Fin n`
has at least 2 elements.
"

/-- Among n+1 elements mapping to n targets, some fiber has size >= 2. -/
Statement (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ b : Fin n, 1 < (Finset.univ.filter (fun a : Fin (n + 1) => f a = b)).card := by
  -- Step 1: Assume for contradiction
  Hint "We prove this by contradiction. Assume no fiber has
  size >= 2, then derive a contradiction from the fiber sum.
  Start with `by_contra` to assume the negation."
  Hint (hidden := true) "Try `by_contra hall`."
  by_contra hall
  Hint "Now use `push_neg` (Level 15) to transform `hall` from
  `not (exists b, 1 < ...)` into `forall b, ... <= 1`."
  Hint (hidden := true) "Try `push_neg at hall`."
  push_neg at hall
  -- hall : ∀ b, (univ.filter ...).card ≤ 1
  -- Step 2: Fiber decomposition
  Hint "Now apply fiber decomposition. To use
  `card_eq_sum_card_fiberwise`, you need a proof that every
  element of `Fin (n+1)` maps into `Finset.univ : Finset (Fin n)`.
  Create this membership proof as a `have`."
  Hint (hidden := true) "Try:
  `have hmem : forall x in (Finset.univ : Finset (Fin (n + 1))), f x in (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ x ∈ (Finset.univ : Finset (Fin (n + 1))),
    f x ∈ (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _
  Hint "Now apply fiber decomposition."
  Hint (hidden := true) "Try:
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`"
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify `hfib` by evaluating `(Finset.univ).card`
  to `Fintype.card (Fin (n+1))` and then to `n + 1`."
  Hint (hidden := true) "Try:
  `rw [Finset.card_univ, Fintype.card_fin] at hfib`"
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  -- hfib : n + 1 = ∑ b ∈ univ, (univ.filter ...).card
  -- Step 3: Sum bound
  Hint "Now bound the sum using `hall` and `sum_le_sum` (Level 13).
  Since every fiber has size <= 1, the sum of fiber sizes is at
  most the number of fibers times 1."
  Hint (hidden := true) "Try:
  `have hbound := Finset.sum_le_sum (fun (b : Fin n) (_ : b in Finset.univ) => hall b)`"
  have hbound := Finset.sum_le_sum (fun (b : Fin n) (_ : b ∈ Finset.univ) => hall b)
  Hint "Simplify the constant sum: `sum b in univ, 1` equals
  `Fintype.card (Fin n) * 1` via `sum_const` and `smul_eq_mul`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound`"
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  -- hbound : ∑ ... ≤ n * 1
  -- hfib : n + 1 = ∑ ...
  -- Together: n + 1 ≤ n * 1 = n, contradiction
  Hint "Now `omega` sees the contradiction:
  `n + 1 = sum <= n * 1`, but `n + 1 > n`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The averaging argument:
1. `by_contra` + `push_neg` — assume all fibers have size <= 1
2. Membership proof: `fun _ _ => Finset.mem_univ _`
3. `card_eq_sum_card_fiberwise` — fiber sum equals source size (n+1)
4. `sum_le_sum` — bound sum by constant sum (using the assumption)
5. `sum_const` + `smul_eq_mul` — constant sum = n * 1 = n
6. `omega` — contradiction: n + 1 <= n is false

**The big picture**: You've just proved that pigeonhole is a
consequence of double counting:
- **Double counting** gives the equation: sum of fiber sizes = n + 1
- **Averaging** gives the bound: if all fibers are small, sum <= n
- **Contradiction** gives the conclusion: some fiber must be large

**The counting contradiction pattern**: This is the third time
you've used this strategy: assume a property, extract a numerical
bound, show the bound is absurd. You saw it in Level 5 (surjection
bound + contradiction) and Level 8 (injection bound + contradiction).
Here: fiber bound + contradiction. The pattern is always:
1. Assume the negation
2. Derive a numerical consequence
3. Show the consequence contradicts known arithmetic

This is one of the most powerful proof patterns in combinatorics.
The averaging argument extends it: in graph theory, 'some vertex
has degree >= the average degree' follows from exactly this logic.

**New tool**: `Finset.sum_le_sum` lets you bound a sum
term-by-term. If you know each `f(x) <= g(x)`, then
`sum f <= sum g`. This is the discrete analogue of comparing
integrals.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Force the fiber approach — disable direct pigeonhole
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
