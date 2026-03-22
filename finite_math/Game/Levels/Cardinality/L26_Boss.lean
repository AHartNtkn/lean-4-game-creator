import Game.Metadata

World "Cardinality"
Level 26

Title "Boss: Cardinality Chain"

Introduction "
# Boss: Chaining the Card Lemmas

You have a full cardinality toolkit. This boss tests whether you can
chain multiple card lemmas together in a single proof.

**The setup**: You have finsets `s` and `t` with known sizes and overlap.
A subset `u` of the set difference `s \\ t` is given. An element `a`
is known to belong to `t`.

**Your task**: Prove a single inequality that requires FOUR cardinality
facts working together:

1. **Complement counting** (`card_sdiff_add_card_inter`): figure out
   `|(s \\ t)|` from `|s|` and `|s \\cap t|`
2. **Monotonicity** (`card_le_card`): bound `|u|` since `u \\subseteq s \\ t`
3. **Erase** (`card_erase_of_mem`): figure out `|t.\\text{erase}\\;a|`
   since `a \\in t`
4. **Inclusion-exclusion** (`card_union_add_card_inter`): figure out
   `|s \\cup t|` from the individual sizes and overlap

Bring all four facts into context with `have`, then let `omega`
combine them.
"

/-- Chain four card lemmas to prove an inequality. -/
Statement (s t u : Finset ℕ) (a : ℕ) (ha : a ∈ t)
    (hs : s.card = 10) (ht : t.card = 6) (hi : (s ∩ t).card = 4)
    (hsub : u ⊆ s \ t) :
    u.card + (t.erase a).card ≤ (s ∪ t).card := by
  Hint "You need four cardinality facts. Start with complement counting:
  `have h1 := Finset.card_sdiff_add_card_inter s t`"
  Hint (hidden := true) "The four `have` statements you need:
  `have h1 := Finset.card_sdiff_add_card_inter s t`
  `have h2 := Finset.card_le_card hsub`
  `have h3 := Finset.card_erase_of_mem ha`
  `have h4 := Finset.card_union_add_card_inter s t`
  Then `omega`."
  have h1 := Finset.card_sdiff_add_card_inter s t
  Hint "Good. `h1 : (s \\ t).card + (s \\cap t).card = s.card`.
  With `hs` and `hi`, this gives `(s \\ t).card = 6`.

  Now bound `u.card` using monotonicity."
  have h2 := Finset.card_le_card hsub
  Hint "Good. `h2 : u.card \\leq (s \\ t).card`.

  Now compute the erase cardinality."
  have h3 := Finset.card_erase_of_mem ha
  Hint "Good. `h3 : (t.erase a).card = t.card - 1`.

  Finally, apply inclusion-exclusion for the union."
  have h4 := Finset.card_union_add_card_inter s t
  Hint "`omega` can now combine all four facts with the given sizes."
  omega

Conclusion "
You chained four card lemmas in a single proof:

| Step | Lemma | What it gave |
|---|---|---|
| 1 | `card_sdiff_add_card_inter` | $|s \\setminus t| + 4 = 10$, so $|s \\setminus t| = 6$ |
| 2 | `card_le_card` | $|u| \\leq |s \\setminus t| = 6$ |
| 3 | `card_erase_of_mem` | $|t.\\text{erase}\\;a| = 6 - 1 = 5$ |
| 4 | `card_union_add_card_inter` | $|s \\cup t| + 4 = 16$, so $|s \\cup t| = 12$ |

Then `omega` combined: $|u| + 5 \\leq 6 + 5 = 11 \\leq 12$. ✓

This is the general cardinality proof strategy: **collect card facts
into the context, then let omega combine them**. The mathematical
thinking goes into choosing which lemmas to apply and in what order;
the arithmetic is mechanical.

Your complete cardinality toolkit:

| Lemma | What it says |
|---|---|
| `card_empty` | $|\\emptyset| = 0$ |
| `card_singleton` | $|\\{a\\}| = 1$ |
| `card_insert_of_notMem` | inserting a new element adds 1 |
| `card_range` | $|\\{0, \\ldots, n-1\\}| = n$ |
| `card_erase_of_mem` | erasing an existing element subtracts 1 |
| `card_le_card` | subsets have $\\leq$ cardinality |
| `card_union_add_card_inter` | inclusion-exclusion |
| `card_union_of_disjoint` | $|s \\cup t| = |s| + |t|$ when disjoint |
| `card_sdiff_add_card_inter` | complement counting |
| `card_product` | $|s \\times^s t| = |s| \\cdot |t|$ |
| `card_pos` | $0 < |s| \\leftrightarrow s.\\text{Nonempty}$ |
| `card_eq_zero` | $|s| = 0 \\leftrightarrow s = \\emptyset$ |
| `filter_subset` | $s.\\text{filter}\\;p \\subseteq s$ (combine with `card_le_card`) |
| `card_univ` | $|\\text{univ}| = \\text{Fintype.card}\\;\\alpha$ |
| `card_fin` | $\\text{Fintype.card}\\;(\\text{Fin}\\;n) = n$ |
| `subset_univ` | every finset is a subset of univ |
| `eq_of_subset_of_card_le` | subset + same size = equal |

**What's next**: You've learned to count *how many* elements a finset
has. The natural next question: what if you want to *add up a value*
at each element? That's the big operator $\\sum_{x \\in s} f(x)$,
written `\\sum x \\in s, f x` in Lean. Big operators turn counting
into computation — and they're built on exactly the card lemma
pattern you just mastered.

The course continues with:
- The **Abstraction Ladder** — the List -> Multiset -> Finset structure
- **Fintype** — counting elements of composite types
- **Big operators** — sums and products over finsets
- **Combinatorics** — binomial coefficients, powerset counting, and the binomial theorem

Phases 4-7 are under construction. Phases 1-3 (Fin, Finset, Cardinality)
are complete.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.card_filter_le Finset.card_le_univ
