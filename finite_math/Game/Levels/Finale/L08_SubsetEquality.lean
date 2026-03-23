import Game.Metadata

World "Finale"
Level 8

Title "Subset Equality"

Introduction "
# When a Subset Is the Whole Set

Levels 5 and 6 used cardinality reasoning to derive
**contradictions** — the image is too large, or the sum of
fibers is too large.

Now you will use the same cardinality tools in the opposite
direction: to derive **equality**. This is the **cardinality
sandwich** — a proof pattern you will use twice more (in the
boss and in the surjective-implies-injective level). Watch for
the three-step shape: compute image size, note subset, apply
`eq_of_subset_of_card_le`.

**The principle**: if $A \\subseteq B$ and $|A| \\ge |B|$, then
$A = B$. A subset that is at least as large as the whole set
must BE the whole set.

This is `Finset.eq_of_subset_of_card_le` from the Cardinality
world. In Cardinality Level 24, you used it for `Fin 5`. Now
prove it works for all `n`.

**The proof plan** (same pattern as Cardinality L24):
1. Compute $|\\text{image}\\,f\\,\\text{univ}| = n$ using injectivity
2. Note $\\text{image}\\,f\\,\\text{univ} \\subseteq \\text{univ}$
3. Apply `eq_of_subset_of_card_le`: subset + same size = equality
"

/-- An injective endofunction maps univ to univ. -/
Statement (n : ℕ) (f : Fin n → Fin n) (hf : Function.Injective f) :
    Finset.univ.image f = Finset.univ := by
  -- Step 1: |image f univ| = n
  Hint "Compute the image size using `card_image_of_injective`."
  Hint (hidden := true) "Try:
  `have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hf`
  `rw [Finset.card_univ, Fintype.card_fin] at himg`"
  have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hf
  rw [Finset.card_univ, Fintype.card_fin] at himg
  -- Step 2: image ⊆ univ
  Hint "The image sits inside `Finset.univ`."
  Hint (hidden := true) "Try
  `have hsub := Finset.subset_univ (Finset.univ.image f)`."
  have hsub := Finset.subset_univ (Finset.univ.image f)
  -- Step 3: Apply eq_of_subset_of_card_le
  Hint "A subset with at least as many elements as the whole set
  must BE the whole set. Use `eq_of_subset_of_card_le`.
  You need to show `univ.card <= (image f univ).card`."
  Hint (hidden := true) "Try:
  `apply Finset.eq_of_subset_of_card_le hsub`
  then close the cardinality bound with
  `rw [Finset.card_univ, Fintype.card_fin, himg]`."
  apply Finset.eq_of_subset_of_card_le hsub
  Hint "Show `univ.card <= (image f univ).card`. Both sides
  equal `n` — simplify and close."
  Hint (hidden := true) "Try
  `rw [Finset.card_univ, Fintype.card_fin, himg]`."
  rw [Finset.card_univ, Fintype.card_fin, himg]

Conclusion "
**Subset equality**: if $A \\subseteq B$ and $|A| \\ge |B|$,
then $A = B$.

| Step | Tool | Result |
|------|------|--------|
| 1 | `card_image_of_injective` | $|f(\\text{univ})| = n$ |
| 2 | `subset_univ` | $f(\\text{univ}) \\subseteq \\text{univ}$ |
| 3 | `eq_of_subset_of_card_le` | $f(\\text{univ}) = \\text{univ}$ |

This is the **cardinality sandwich** — the equality direction of
cardinality reasoning: if $A \\subseteq B$ and $|A| \\ge |B|$,
then $A = B$. The subset provides one inequality, the cardinality
bound provides the other, and equality is 'sandwiched' between
them.

In Levels 5 and 6, you used cardinality to derive contradictions
(the pigeonhole direction). Here you derived a positive result:
because the image has exactly the right number of elements, it
must be the entire codomain.

**Why this matters for the boss**: The boss proves that an
injective endofunction on `Fin n` is surjective. The crucial
step is exactly this — the cardinality sandwich showing
`image f univ = univ`. You just practiced that step in
isolation.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent library pigeonhole shortcuts
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt Finite.surjective_of_injective Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective Finset.eq_univ_of_card Finset.map_eq_of_subset
