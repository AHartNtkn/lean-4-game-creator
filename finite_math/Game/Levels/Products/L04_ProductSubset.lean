import Game.Metadata

World "Products"
Level 4

Title "Product Subset Monotonicity"

Introduction "
# Bigger Factors, Bigger Products

If `s ⊆ s'` and `t ⊆ t'`, does `s ×ˢ t ⊆ s' ×ˢ t'`?

Of course — if every element of `s` is in `s'` and every element
of `t` is in `t'`, then every pair from `s ×ˢ t` is in `s' ×ˢ t'`.

Prove this by introducing a pair, extracting its components
from `s ×ˢ t`, and rebuilding membership in `s' ×ˢ t'`.

**New move**: This level combines `mem_product` extraction with
`mk_mem_product` construction — the full round-trip.
"

/-- Product preserves subset inclusion. -/
Statement (s s' t t' : Finset ℕ)
    (hs : s ⊆ s') (ht : t ⊆ t') :
    s ×ˢ t ⊆ s' ×ˢ t' := by
  Hint "To prove `s ×ˢ t ⊆ s' ×ˢ t'`, introduce an element
  and its membership hypothesis."
  Hint (hidden := true) "Try `intro p hp`."
  intro p hp
  Hint "Now extract the components from `hp : p ∈ s ×ˢ t`."
  Hint (hidden := true) "Try `rw [Finset.mem_product] at hp`."
  rw [Finset.mem_product] at hp
  Hint "You have `hp : p.1 ∈ s ∧ p.2 ∈ t`. Build membership
  in `s' ×ˢ t'` by applying the subset hypotheses to each component."
  Hint (hidden := true) "Try `exact Finset.mk_mem_product (hs hp.1) (ht hp.2)`."
  exact Finset.mk_mem_product (hs hp.1) (ht hp.2)

Conclusion "
You've just used the **membership round-trip** pattern:

1. **Extract**: `rw [Finset.mem_product] at hp` → get component memberships
2. **Transform**: apply `hs` and `ht` to promote to the larger sets
3. **Rebuild**: `Finset.mk_mem_product` assembles the new product membership

This extract-transform-rebuild pattern is one of the most common
proof shapes in finset arguments. You'll see it again whenever you
need to move membership from one structured set to another — including
the off-diagonal levels later in this world.
"

/-- `gcongr` (generalized congruence) solves monotonicity goals
like `f a ≤ f b` when `a ≤ b` and `f` is known to be monotone.

Disabled in this level to force manual extraction and rebuilding.
-/
TacticDoc gcongr

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith gcongr
DisabledTheorem Finset.product_subset_product Finset.product_subset_product_left Finset.product_subset_product_right
