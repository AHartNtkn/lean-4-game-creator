import Game.Metadata

World "BigOpAlgebra"
Level 18

Title "Boss: Algebraic Manipulation"

Introduction "
# Boss: Putting It All Together

Prove this algebraic identity about sums over a disjoint union:

$$\\Bigl(\\sum_{x \\in s \\cup t} (f(x) + f(x) + 1)\\Bigr) \\cdot |s \\cup t| = (2a + 2b) \\cdot |s \\cup t| + |s \\cup t|^2$$

where $a = \\sum_{x \\in s} f(x)$ and $b = \\sum_{x \\in t} f(x)$.

This requires integrating five distinct skills:

1. **sum_add_distrib** — split the summand (twice)
2. **← card_eq_sum_ones** — convert `∑ 1` to cardinality
3. **sum_union** — split the union sum using disjointness
4. **Hypothesis substitution** — plug in known values
5. **ring** — close the final algebra

You can solve this with a chain of `rw` calls, or organize it
as a `calc` block for readability. Both are valid.
"

/-- Integrate sum_add_distrib, card_eq_sum_ones, sum_union, and ring. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ) (a b : ℕ) (h : Disjoint s t)
    (hs : ∑ x ∈ s, f x = a) (ht : ∑ x ∈ t, f x = b) :
    (∑ x ∈ s ∪ t, (f x + f x + 1)) * (s ∪ t).card =
    (2 * a + 2 * b) * (s ∪ t).card + (s ∪ t).card ^ 2 := by
  Hint "The summand `f x + f x + 1` has the form `(f x + f x) + 1`.
  Use `rw [Finset.sum_add_distrib]` to split the outermost `+`.
  You'll use `ring` at the end to close the algebra."
  Hint (hidden := true) "**rw approach**: Start with
  `rw [Finset.sum_add_distrib]` to split the outermost `+`."
  Hint (hidden := true) "**calc approach**: You can also organize
  this as a calc block. The chain is:
  (1) `sum_add_distrib` to split off `∑ 1`,
  (2) `sum_add_distrib` again to split `∑(f + f)`,
  (3) `← card_eq_sum_ones` to convert `∑ 1` to card,
  (4) `sum_union h` to split the union sums,
  (5) `rw [hs, ht]` to substitute,
  (6) `ring` to close."
  Branch
    calc (∑ x ∈ s ∪ t, (f x + f x + 1)) * (s ∪ t).card
        = ((∑ x ∈ s ∪ t, (f x + f x)) + ∑ x ∈ s ∪ t, 1) *
          (s ∪ t).card := by
            rw [Finset.sum_add_distrib]
      _ = (((∑ x ∈ s ∪ t, f x) + ∑ x ∈ s ∪ t, f x) +
          ∑ x ∈ s ∪ t, 1) * (s ∪ t).card := by
            rw [Finset.sum_add_distrib]
      _ = (((∑ x ∈ s ∪ t, f x) + ∑ x ∈ s ∪ t, f x) +
          (s ∪ t).card) * (s ∪ t).card := by
            rw [← Finset.card_eq_sum_ones]
      _ = ((((∑ x ∈ s, f x) + ∑ x ∈ t, f x) +
           ((∑ x ∈ s, f x) + ∑ x ∈ t, f x)) +
          (s ∪ t).card) * (s ∪ t).card := by
            rw [Finset.sum_union h]
      _ = (((a + b) + (a + b)) + (s ∪ t).card) *
          (s ∪ t).card := by rw [hs, ht]
      _ = (2 * a + 2 * b) * (s ∪ t).card +
          (s ∪ t).card ^ 2 := by ring
  rw [Finset.sum_add_distrib]
  Hint "The first sum still has `f x + f x`. Apply
  `sum_add_distrib` again."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now use `← card_eq_sum_ones` to convert `∑ 1` to
  cardinality."
  Hint (hidden := true) "Try `rw [← Finset.card_eq_sum_ones]`."
  rw [← Finset.card_eq_sum_ones]
  Hint "Split the union sums using `sum_union` with the
  disjointness hypothesis `h`."
  Hint (hidden := true) "Try `rw [Finset.sum_union h]`."
  rw [Finset.sum_union h]
  Hint "Substitute the known sum values."
  Hint (hidden := true) "Try `rw [hs, ht]`."
  rw [hs, ht]
  Hint "Close the algebra with `ring`. The multiplication by
  `(s ∪ t).card` makes this a nonlinear identity that only
  `ring` can handle."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
Congratulations! You've mastered the algebraic manipulation of
big operators.

**The proof pattern you just used**:
1. `sum_add_distrib` (possibly repeatedly) to decompose the summand
2. `← card_eq_sum_ones` to convert `∑ 1` to cardinality
3. `sum_union` to split by disjoint union
4. Hypothesis substitution to plug in known values
5. `ring` to close the algebra

**Your complete BigOpAlgebra toolkit**:

| Lemma | What it does |
|-------|-------------|
| `sum_add_distrib` | `∑(f + g) = ∑f + ∑g` |
| `prod_mul_distrib` | `∏(f · g) = ∏f · ∏g` |
| `sum_const` | `∑ c = card • c` |
| `prod_const` | `∏ c = c ^ card` |
| `sum_union h` | `∑(s ∪ t) = ∑s + ∑t` (disjoint) |
| `prod_union h` | `∏(s ∪ t) = ∏s · ∏t` (disjoint) |
| `sum_filter p f` | Filtered ↔ conditional sum |
| `sum_comm` | `∑_x ∑_y = ∑_y ∑_x` |
| `sum_range_succ` | `∑ range (n+1) = ∑ range n + f n` |

| Tactic | What it does |
|--------|-------------|
| `calc` | Chain multi-step equalities |
| `ring` | Close algebraic goals |
| `ring_nf` | Normalize ring expressions |

**Looking ahead**: Everything you proved here used pre-existing
algebraic lemmas — you transformed sums by applying known
identities. But what about identities that *don't* have a
library lemma? The next world (FinsetInduction) teaches a
fundamentally different approach: proving sum identities by
**induction on finsets**. Combined with `sum_range_succ`, this
lets you prove formulas like $\\sum_{{i=0}}^{{n}} i = n(n+1)/2$
from scratch — no library lemma needed.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
