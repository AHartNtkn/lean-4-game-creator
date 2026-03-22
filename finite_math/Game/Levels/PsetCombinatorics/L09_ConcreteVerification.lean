import Game.Metadata

World "PsetCombinatorics"
Level 9

Title "Concrete Verification"

Introduction "
# Check the Numbers

You've proved several identities symbolically. Now **verify**
one concretely: check that the absorption identity holds for
$n = 4, k = 2$ by computing both sides.

$$(n + 1) \\cdot \\binom{n}{k} = \\binom{n+1}{k+1} \\cdot (k + 1)$$

For $n = 4, k = 2$:
- LHS: $5 \\cdot \\binom{4}{2} = 5 \\cdot 6 = 30$
- RHS: $\\binom{5}{3} \\cdot 3 = 10 \\cdot 3 = 30$ ✓

But we add a powerset layer: given $|s| = 4$, prove that
$5 \\cdot |\\text{powersetCard } 2\\ s| = 3 \\cdot 10$.

The concrete values force you through the strip-and-apply
pattern one more time, but now you can **predict** the answer
before Lean confirms it.
"

/-- Verify the absorption identity concretely for n = 4, k = 2. -/
Statement (s : Finset ℕ) (hs : s.card = 4) :
    5 * (Finset.powersetCard 2 s).card = 3 * 10 := by
  Hint "Strip the powerset layer as usual."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard, hs]`."
  rw [Finset.card_powersetCard, hs]
  Hint "The goal is `5 * Nat.choose 4 2 = 3 * 10`.

  Both sides are concrete numbers. You could apply the absorption
  identity, but here the values are small enough that the kernel
  reduces them directly."
  Hint (hidden := true) "Both sides reduce to 30. Try `rfl`."
  rfl

Conclusion "
Both sides are 30. The absorption identity
$(n+1) \\cdot C(n, k) = C(n+1, k+1) \\cdot (k+1)$ passes the
sanity check: $5 \\cdot 6 = 10 \\cdot 3 = 30$.

Concrete verification builds trust in symbolic proofs. When you
prove an identity for all $n$, checking a specific case confirms
you haven't made a sign error or an off-by-one mistake. The next
levels return to symbolic proofs with this grounding in place.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
