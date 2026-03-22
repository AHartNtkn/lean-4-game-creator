import Game.Metadata

World "FinsetInduction"
Level 4

Title "A Complete Induction Proof"

Introduction "
# Putting It Together: ∑ 1 = card

Time to write a complete finset induction proof from start to finish.

You'll prove that **the sum of 1 over any finset equals the finset's
cardinality**:

$$\\sum_{x \\in s} 1 = |s|$$

You already know `card_eq_sum_ones` as a *theorem* — but here you'll
*prove* it by induction, which is how such theorems are established
in the first place.

**The proof plan**:
- **Base case**: `\\sum_{x \\in \\emptyset} 1 = 0 = |\\emptyset|`
- **Inductive step**: `\\sum_{x \\in \\text{insert } a\\ s} 1 = 1 + \\sum_{x \\in s} 1
  = 1 + |s| = |\\text{insert } a\\ s|`

For the inductive step, you'll need the lemma you learned in the
Cardinality world:

```
Finset.card_insert_of_notMem : a \\notin s \\to (insert a s).card = s.card + 1
```

This is the cardinality analogue of `sum_insert`: inserting a fresh
element increases the cardinality by 1.
"

/-- The sum of 1 over any finset equals its cardinality. -/
Statement (s : Finset ℕ) : ∑ _x ∈ s, (1 : ℕ) = s.card := by
  Hint "Start with finset induction on `s`."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: rewrite both `sum_empty` and `card_empty`."
    Hint (hidden := true) "Try `rw [Finset.sum_empty, Finset.card_empty]`."
    rw [Finset.sum_empty, Finset.card_empty]
  | @insert a s ha ih =>
    Hint "**Inductive step**: You need three rewrites:
    1. `Finset.sum_insert ha` — peel the sum
    2. `Finset.card_insert_of_notMem ha` — peel the cardinality
    3. `ih` — apply the induction hypothesis

    Then close the arithmetic."
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih]`
    then `omega`."
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih]
    Hint "The goal is `1 + s.card = s.card + 1`. Use `omega` to close."
    Hint (hidden := true) "Try `omega`."
    omega

Conclusion "
You've proved `\\sum_{x \\in s} 1 = |s|` from scratch by induction!
This is exactly `card_eq_sum_ones` — the same theorem you used as a
library fact in BigOpIntro. There, you cited it; here, you proved it
by induction. This is how such theorems are established in the
library in the first place.

**The complete pattern** you used:
1. `induction s using Finset.induction_on`
2. Base: `sum_empty` + `card_empty`
3. Step: `sum_insert ha` + `card_insert_of_notMem ha` + `ih`
4. Close with `omega`

**Concrete trace**: To make the abstract pattern concrete, imagine
$s = \\{1, 2, 3\\}$. Finset induction builds up from the empty set:

| Step | Finset | Sum of 1s | Card | Match? |
|------|--------|-----------|------|--------|
| Base | $\\emptyset$ | $0$ | $0$ | $\\checkmark$ |
| Insert 3 | $\\{3\\}$ | $1 + 0 = 1$ | $0 + 1 = 1$ | $\\checkmark$ |
| Insert 2 | $\\{2, 3\\}$ | $1 + 1 = 2$ | $1 + 1 = 2$ | $\\checkmark$ |
| Insert 1 | $\\{1, 2, 3\\}$ | $1 + 2 = 3$ | $2 + 1 = 3$ | $\\checkmark$ |

Each step applies `sum_insert` (peeling the sum) and
`card_insert_of_notMem` (peeling the cardinality), then the IH
gives the equality for the smaller set. The concrete trace shows
that the abstract machinery does exactly what you'd expect.

Notice that `omega` handled `1 + s.card = s.card + 1` (commutativity
of addition over natural numbers). For more complex arithmetic,
you'll need `ring`.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_const_zero Finset.sum_add_distrib Finset.sum_range_sub Finset.eq_sum_range_sub
