import Game.Metadata

World "Products"
Level 3

Title "Extracting from Products"

Introduction "
# The Backward Direction

Now let's use `Finset.mem_product` in the other direction.
If you **know** that a pair belongs to a product, you can
extract the component memberships.

Given `h : p ∈ s ×ˢ t`, rewriting with `Finset.mem_product`
at `h` gives `h : p.1 ∈ s ∧ p.2 ∈ t`. Then you can use
`obtain ⟨h1, h2⟩ := h` to split the conjunction.

**Lean tip: dot-notation for conjunctions**. If `h : A ∧ B`, then
`h.1` is the left conjunct (a proof of `A`) and `h.2` is the right
conjunct (a proof of `B`). For nested conjunctions like
`h : A ∧ B ∧ C`, you can chain: `h.1` is `A`, `h.2.1` is `B`,
`h.2.2` is `C`. This is a shorthand for `obtain ⟨h1, h2⟩ := h`
followed by `exact h1`.

**Your task**: Given that `p ∈ s ×ˢ t`, prove that `p.1 ∈ s`.
"

/-- Extract the first component membership from a product membership. -/
Statement (s : Finset ℕ) (t : Finset ℕ) (p : ℕ × ℕ) (h : p ∈ s ×ˢ t) :
    p.1 ∈ s := by
  Hint "Rewrite `Finset.mem_product` at `h` to expose the
  conjunction `p.1 ∈ s ∧ p.2 ∈ t`."
  Hint (hidden := true) "Try `rw [Finset.mem_product] at h`."
  rw [Finset.mem_product] at h
  Hint "Now `h : p.1 ∈ s ∧ p.2 ∈ t`. Extract the left conjunct."
  Hint (hidden := true) "Try `obtain ⟨h1, h2⟩ := h` then `exact h1`.
  Or use `exact h.1`."
  exact h.1

Conclusion "
Extraction from products is the reverse of construction. The
pattern is:

1. `rw [Finset.mem_product] at h` — turn product membership into `∧`
2. `exact h.1` or `exact h.2` — extract the component you need

This is how product membership feeds into other reasoning: you
don't work with the product directly, you extract what you need.

**Lean tip**: Since `Finset.mem_product` is an `↔`, you can also
use `.mp` and `.mpr` directly without rewriting:
- `Finset.mem_product.mp h` gives the conjunction `h.1 ∈ s ∧ h.2 ∈ t`
- `Finset.mem_product.mpr ⟨ha, hb⟩` builds product membership

The `.mp`/`.mpr` pattern works with any `↔` lemma and is common
in Lean library proofs. We teach the `rw` + `exact` approach
because it makes the proof state visible at each step.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
