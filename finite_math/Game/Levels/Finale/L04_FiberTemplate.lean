import Game.Metadata

World "Finale"
Level 4

Title "The Fiber Template"

Introduction "
# Fiber Decomposition on Fin Types

A function $f : \\text{Fin}(n+1) \\to \\text{Fin}\\,n$ sorts $n+1$
items into $n$ bins. The **fiber** of bin $j$ is the set of items
mapped to $j$:

$$\\text{fiber}_j = \\{i \\in \\text{Fin}(n+1) \\mid f(i) = j\\}$$

Fiber decomposition says: **the sum of all fiber sizes equals
the total number of items**. Prove this for the Fin-type setting.

You'll need `Finset.card_eq_sum_card_fiberwise`, which requires
a membership proof: every element of the domain maps into the
codomain universe.
"

/-- The sum of fiber sizes equals the domain cardinality. -/
Statement (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∑ j ∈ (Finset.univ : Finset (Fin n)),
      (Finset.univ.filter (fun i : Fin (n + 1) => f i = j)).card = n + 1 := by
  Hint "Every element of `Fin (n+1)` maps into `Finset.univ` of
  `Fin n`. Establish this membership fact."
  Hint (hidden := true) "Try:
  `have hmem : forall i in (Finset.univ : Finset (Fin (n + 1))), f i in (Finset.univ : Finset (Fin n)) := by intro _ _; exact Finset.mem_univ _`"
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
    f i ∈ (Finset.univ : Finset (Fin n)) := by
    intro _ _
    exact Finset.mem_univ _
  Hint "Apply fiber decomposition."
  Hint (hidden := true) "Try
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`."
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify `Finset.univ.card` on the left to `n + 1`
  using `card_univ` and `card_fin`."
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin] at hfib`."
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  Hint "Now `hfib` says `n + 1 = sum of fiber sizes`. The goal
  is the reverse equation."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
**The fiber template** — a three-step pattern you can apply
whenever you need to relate a cardinality to a sum of subgroup
sizes:

1. **Membership proof**: Show every domain element maps into
   the codomain universe (`fun _ _ => Finset.mem_univ _`)
2. **Fiber decomposition**: `card_eq_sum_card_fiberwise` expresses
   `|domain| = sum of |fiber_j|` over all bins `j`
3. **Simplify**: `card_univ` + `card_fin` convert `Finset.univ.card`
   to the concrete size

This template is the foundation of the pigeonhole principle:
if the sum of fiber sizes exceeds what's possible when each
fiber is small, some fiber must be large.

The fiber template also connects to the Products world:
fiber decomposition is a special case of the sigma cardinality
formula `card_sigma`, where each fiber is one slice of a
dependent product.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
