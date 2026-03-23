import Game.Metadata

World "Finale"
Level 5

Title "Quantitative Pigeonhole"

Introduction "
# Some Fiber Must Be Large

If $n + 1$ pigeons sit in $n$ holes, some hole has at least 2
pigeons.

Level 4 introduced the **fiber template** — a three-step pattern
(membership proof, fiber decomposition, simplification) that
converts a cardinality into a sum of fiber sizes. This level
takes the conceptual leap: a sum identity can force an
**existence** result. If the total
$\\sum |\\text{fiber}_j| = n + 1$ but there are only $n$ summands,
then at least one summand must exceed 1.

The proof uses the **contrapositive**: assume every fiber has
size at most 1, bound the sum by $n$, and obtain $n + 1 \\le n$
— contradiction.

**The proof plan**:
1. Assume for contradiction that all fibers have size at most 1
2. Apply the fiber template: $n + 1 = \\sum |\\text{fiber}_j|$
3. Bound the sum: $\\sum |\\text{fiber}_j| \\le \\sum 1 = n$
4. Contradiction: $n + 1 \\le n$
"

/-- Every function from Fin (n+1) to Fin n has a fiber with more than 1 element. -/
Statement (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ c : Fin n,
      1 < (Finset.univ.filter (fun i : Fin (n + 1) => f i = c)).card := by
  -- Step 1: Contradiction setup
  Hint "Assume for contradiction that no fiber has more than 1
  element."
  Hint (hidden := true) "Try `by_contra hall`."
  by_contra hall
  Hint (hidden := true) "Try `push_neg at hall`."
  push_neg at hall
  -- hall : ∀ c, (univ.filter ...).card ≤ 1
  -- Step 2: Fiber decomposition
  Hint "Set up the fiber template from Level 4. Start with the
  membership proof."
  Hint (hidden := true) "Try:
  `have hmem : forall i in (Finset.univ : Finset (Fin (n + 1))), f i in (Finset.univ : Finset (Fin n)) := by intro _ _; exact Finset.mem_univ _`"
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
    f i ∈ (Finset.univ : Finset (Fin n)) := by
    intro _ _
    exact Finset.mem_univ _
  Hint (hidden := true) "Try
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`."
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify `hfib` to get `n + 1 = sum of fiber sizes`."
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin] at hfib`."
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  -- Step 3: Bound the sum
  Hint "Bound the sum using `hall`: each fiber has size at most 1,
  so the sum is at most `n * 1 = n`."
  Hint (hidden := true) "Try
  `have hbound := Finset.sum_le_sum (fun (c : Fin n) (_ : c in Finset.univ) => hall c)`."
  have hbound := Finset.sum_le_sum
    (fun (c : Fin n) (_ : c ∈ Finset.univ) => hall c)
  Hint (hidden := true) "Try
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hbound`."
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hbound
  -- Step 4: Contradiction
  Hint "Now `hfib` says `n + 1 = sum` and `hbound` says
  `sum <= n`. So `n + 1 <= n` — contradiction."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
**The contrapositive of the fiber template**:

| Step | Tool | Result |
|------|------|--------|
| 1 | `by_contra` + `push_neg` | Assume all fibers have size at most 1 |
| 2 | `card_eq_sum_card_fiberwise` | $n + 1 = \\sum |\\text{fiber}_j|$ |
| 3 | `sum_le_sum` + `sum_const` | $\\sum |\\text{fiber}_j| \\le n$ |
| 4 | `omega` | $n + 1 \\le n$ is absurd |

This is the **quantitative pigeonhole principle**: $n + 1$ items
in $n$ bins forces at least one bin to have more than 1 item.

**The contrapositive setup** (`by_contra` + `push_neg`): this
two-tactic opening converts 'there exists X' into 'for all,
not-X.' It is a reusable proof pattern whenever you want to
derive a contradiction from an existence goal. You will see
it again in Levels 7 and 8.

**Connection to Level 4**: Level 4 proved the fiber template
(sum of fiber sizes = total). This level takes the
contrapositive: if the total exceeds what's possible with small
fibers, some fiber must be large. The two levels are logically
equivalent — they are the same fact viewed from opposite
directions.

**In plain mathematics**: if you have more pigeons than holes,
at least one hole contains two or more pigeons. The formal
proof replaces the hand-waving with: decompose into fibers,
bound each fiber, sum the bounds, observe the contradiction.

**The reusable pattern**: This proof uses the **sum identity +
per-term bound** template:
1. Establish a sum identity: $\\sum x_j = N$
2. Assume a per-term bound: each $x_j \\le k$
3. Sum the bounds: $\\sum x_j \\le k \\cdot (\\text{number of terms})$
4. Contradiction: $N > k \\cdot (\\text{number of terms})$

This same template appears beyond pigeonhole — it's the
structure behind **averaging arguments** (if the average
exceeds a threshold, some term must exceed it) and
**probabilistic existence proofs** (if the expected value
of a count is positive, some instance must have a positive count).
"

TheoremTab "Fintype"

/-- `Fintype.exists_ne_map_eq_of_card_lt` is the library version of the
pigeonhole principle: if `Fintype.card α < Fintype.card β` is false
(i.e., the domain is at least as large as the codomain), then any
function `f : α → β` maps two distinct elements to the same output.

Disabled here so you prove pigeonhole from first principles.
-/
TheoremDoc Fintype.exists_ne_map_eq_of_card_lt as "Fintype.exists_ne_map_eq_of_card_lt" in "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent library pigeonhole shortcuts
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
