import Game.Metadata

World "CountingTypes"
Level 11

Title "Boss: Functions vs. Injections"

Introduction "
# Boss: How Many More Functions Than Injections?

You're given a type `α` equivalent to `Fin 2 × Bool` — a domain
with $2 \\cdot 2 = 4$ elements. The target is `Fin 3 ⊕ Bool` — a
codomain with $3 + 2 = 5$ elements.

**All functions** from `α` to the codomain: $5^4 = 625$.

**Injections only**: $5^{\\underline{4}} = 5 \\times 4 \\times 3 \\times 2 = 120$.

**Difference**: $625 - 120 = 505$ non-injective functions.

The 505 non-injective functions are exactly those that 'waste' a slot
by mapping two different inputs to the same output.

**Your task**: Prove this formally. You'll need two `have` statements
to compute each count, then `omega` for the final subtraction.

This integrates every skill from the world: `card_fun`, `card_prod`,
`card_sum`, `card_congr`, `card_embedding_eq`, `descFactorial`,
and the `have + omega` strategy.
"

/-- There are 505 more functions than injections from α to Fin 3 ⊕ Bool,
    given α ≃ Fin 2 × Bool. -/
Statement (α : Type*) [DecidableEq α] [Fintype α]
    (e : α ≃ Fin 2 × Bool) :
    Fintype.card (α → (Fin 3 ⊕ Bool)) - Fintype.card (α ↪ (Fin 3 ⊕ Bool)) = 505 := by
  Hint "This is a subtraction — you need the value of both terms.
  Start by computing the total function count.
  Try `have hfun : Fintype.card (α → (Fin 3 ⊕ Bool)) = 625 := by`"
  Hint (hidden := true) "Enter:
  `have hfun : Fintype.card (α → (Fin 3 ⊕ Bool)) = 625 := by`
  then prove the function count inside the `by` block."
  have hfun : Fintype.card (α → (Fin 3 ⊕ Bool)) = 625 := by
    Hint "Use the decompose-evaluate workflow. Start with
    `rw [Fintype.card_fun]`."
    rw [Fintype.card_fun]
    Hint "Resolve the codomain `Fin 3 ⊕ Bool`:
    `rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]`."
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    Hint "Resolve the abstract domain with `card_congr e`, then
    decompose the product."
    Hint (hidden := true) "Try
    `rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]`
    then `omega`."
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    Hint "The goal is `(3 + 2) ^ (2 * 2) = 625`. Close with `omega`."
    omega
  Hint "Good — 625 functions. Now compute the injection count.
  Try `have hinj : Fintype.card (α ↪ (Fin 3 ⊕ Bool)) = 120 := by`"
  have hinj : Fintype.card (α ↪ (Fin 3 ⊕ Bool)) = 120 := by
    Hint "Convert to a falling factorial with `card_embedding_eq`, then
    resolve the codomain and domain."
    rw [Fintype.card_embedding_eq]
    Hint "Resolve the codomain:
    `rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]`."
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    Hint "Resolve the abstract domain and decompose the product:
    `rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]`."
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    Hint "Now unfold `5.descFactorial 4` — four `descFactorial_succ`
    rewrites plus `descFactorial_zero`."
    Hint (hidden := true) "Try
    `rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`."
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_zero]
  Hint "You have `hfun : ... = 625` and `hinj : ... = 120`.
  Close with `omega`."
  omega

Conclusion "
$$|\\alpha \\to (\\text{Fin}\\;3 \\oplus \\text{Bool})| - |\\alpha \\hookrightarrow (\\text{Fin}\\;3 \\oplus \\text{Bool})| = 5^4 - 5^{\\underline{4}} = 625 - 120 = 505$$

You integrated every skill from this world in one proof:

| Step | Skill | Source level |
|---|---|---|
| `card_fun` | function decomposition | L01 |
| `card_congr e` | equivalence transfer | L02 |
| `card_prod` | product decomposition | L03 |
| `card_sum` | sum decomposition | L04 |
| `descFactorial_succ/zero` | falling factorial unfolding | L05-L06 |
| `descFactorial_self` | falling factorial = factorial | L07 |
| `card_embedding_eq` | embedding to descFactorial | L08-L09 |
| `have` + `omega` | collect-and-close strategy | L10 |

## Your Counting Toolkit

| Lemma | What it does |
|---|---|
| `card_fun` | `card (α → β) = card β ^ card α` |
| `card_prod` | `card (α × β) = card α * card β` |
| `card_sum` | `card (α ⊕ β) = card α + card β` |
| `card_congr e` | `α ≃ β → card α = card β` |
| `card_embedding_eq` | `card (α ↪ β) = (card β).descFactorial (card α)` |
| `card_fin n` | `card (Fin n) = n` |
| `card_bool` | `card Bool = 2` |
| `descFactorial_succ` | `n.descFactorial (k+1) = (n-k) * n.descFactorial k` |
| `descFactorial_zero` | `n.descFactorial 0 = 1` |

**Looking ahead**: Cardinality can also be viewed as a sum:
`s.card = ∑ x ∈ s, 1`. This connection between counting and
summation will be central when big operators are introduced.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Force full recursive unfolding in boss
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
