import Game.Metadata

World "Finale"
Level 10

Title "Support Bounding via Calc"

Introduction "
# Bounding the Support of a Sum

A finitely supported function `f : alpha ->0 M` is nonzero at
only finitely many points. The support `f.support` is the
Finset of those points.

When you add two finitely supported functions, the sum can
only be nonzero where at least one summand was nonzero. So
the support of `f + g` sits inside `f.support ∪ g.support`.

**Claim**: `|support(f + g)| <= |support(f)| + |support(g)|`.

**The proof plan** uses a `calc` chain to express the inequality
as two steps:

$$|\\text{support}(f + g)| \\le |\\text{support}(f) \\cup \\text{support}(g)| \\le |\\text{support}(f)| + |\\text{support}(g)|$$

Each step uses one inequality:
1. `Finsupp.support_add` + `card_le_card` : subset gives first `<=`
2. `card_union_add_card_inter` : union bound gives second `<=`
"

/-- The support of a sum is bounded by the sum of supports. -/
Statement (f g : ℕ →₀ ℕ) :
    (f + g).support.card ≤ f.support.card + g.support.card := by
  Hint "Use a `calc` chain to express this as two inequalities:
  `|support(f+g)| <= |support(f) ∪ support(g)| <= |support(f)| + |support(g)|`."
  Hint (hidden := true) "Try:
  `calc (f + g).support.card`
  `    <= (f.support ∪ g.support).card := Finset.card_le_card Finsupp.support_add`
  `  _ <= f.support.card + g.support.card := by`
  `        have h := Finset.card_union_add_card_inter f.support g.support`
  `        omega`"
  calc (f + g).support.card
      ≤ (f.support ∪ g.support).card := by
        Hint "The support of `f + g` is a subset of `f.support ∪ g.support`
        (by `Finsupp.support_add`). Convert subset to cardinality inequality."
        Hint (hidden := true) "Try `exact Finset.card_le_card Finsupp.support_add`."
        exact Finset.card_le_card Finsupp.support_add
    _ ≤ f.support.card + g.support.card := by
        Hint "Bound the union size: `|A ∪ B| + |A ∩ B| = |A| + |B|`,
        so `|A ∪ B| <= |A| + |B|`."
        Hint (hidden := true) "Try:
        `have h := Finset.card_union_add_card_inter f.support g.support`
        then `omega`."
        have h := Finset.card_union_add_card_inter f.support g.support
        omega

Conclusion "
**Support bounding via calc**:

```
calc |support(f+g)|
    <= |support(f) ∪ support(g)|  -- subset bound
  _ <= |support(f)| + |support(g)| -- union bound
```

| Step | Tool | Result |
|------|------|--------|
| 1 | `support_add` + `card_le_card` | `|support(f+g)| <= |union|` |
| 2 | `card_union_add_card_inter` + `omega` | `|union| <= |A| + |B|` |

**Why calc**: The `calc` block makes the inequality chain explicit.
Instead of accumulating `have` hypotheses and closing with `omega`,
each step states its own intermediate result. This is the same
`calc` technique you learned in the SummationFormulas world, now
applied to `<=` (not just `=`).

This level integrates three phases:
- **Phase 6** (Finsupp): `support_add` tells you WHERE the sum
  can be nonzero
- **Phase 2** (Finset): the union operation combines supports
- **Phase 3** (Cardinality): `card_le_card` and
  `card_union_add_card_inter` give the size bound

The support-bounding pattern appears throughout algebra:
- **Polynomial degree bounds**: deg(p + q) <= max(deg p, deg q)
  follows from the same support containment
- **Sparse linear algebra**: the number of nonzero entries in
  a vector sum is at most the total from both vectors
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Lattice aliases for Finset operations
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_le inf_sup_right inf_sup_left sup_inf_right sup_inf_left sup_eq_left inf_eq_left
