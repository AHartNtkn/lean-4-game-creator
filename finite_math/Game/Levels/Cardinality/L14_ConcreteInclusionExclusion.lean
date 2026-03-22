import Game.Metadata

World "Cardinality"
Level 14

Title "Concrete Inclusion-Exclusion"

Introduction "
# Inclusion-Exclusion with Actual Numbers

Level 13 proved an abstract inclusion-exclusion problem using the
'collect card facts, then omega' strategy. Here you'll apply the
same idea to **concrete finsets** — finsets you can see the elements of.

Now ground the formula with **concrete finsets** — finsets you can
see the elements of.

Take `s = {1, 2, 3}` and `t = {2, 3, 4}`. You can verify by
inspection:
- $|s| = 3$
- $|t| = 3$
- $s \\cap t = \\{2, 3\\}$, so $|s \\cap t| = 2$
- $s \\cup t = \\{1, 2, 3, 4\\}$, so $|s \\cup t| = 4$

Check: $|s| + |t| - |s \\cap t| = 3 + 3 - 2 = 4 = |s \\cup t|$. ✓

The proof doesn't require computing each cardinality separately.
Just bring in `card_union_add_card_inter` and let `decide` handle
the concrete arithmetic.

**Your task**: Prove that $|\\{1,2,3\\} \\cup \\{2,3,4\\}| = 4$.
"

/-- The union of {1,2,3} and {2,3,4} has 4 elements. -/
Statement : (({1, 2, 3} : Finset ℕ) ∪ {2, 3, 4}).card = 4 := by
  Branch
    decide
  Hint "Use `card_union_add_card_inter` to bring the inclusion-exclusion
  identity into context, then let `omega` (or `decide`) handle the
  concrete arithmetic."
  Hint (hidden := true) "Try
  `have h := Finset.card_union_add_card_inter s t` where `s` and `t`
  are your two concrete finsets. Since these are concrete, `decide` can
  close the remaining goal. The simplest approach: just `decide`."
  have h := Finset.card_union_add_card_inter ({1, 2, 3} : Finset ℕ) {2, 3, 4}
  decide

Conclusion "
You applied inclusion-exclusion to **concrete** finsets and verified
the arithmetic:

$$|\\{1,2,3\\} \\cup \\{2,3,4\\}| + |\\{1,2,3\\} \\cap \\{2,3,4\\}| = |\\{1,2,3\\}| + |\\{2,3,4\\}|$$
$$4 + 2 = 3 + 3$$

The formula corrects for double-counting: elements $2$ and $3$ appear
in both sets, so adding $|s| + |t|$ counts them twice. Subtracting
$|s \\cap t| = 2$ fixes the overcount.

**The calculation tool**: For concrete finsets, `decide` can verify
cardinality equalities directly — Lean just computes and checks. But
`card_union_add_card_inter` is the tool that scales: it works for
*symbolic* finsets where you can't compute directly, as you saw in
Level 13.

Next: what happens when the overlap is empty?
"

TheoremTab "Card"

DisabledTactic trivial native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
