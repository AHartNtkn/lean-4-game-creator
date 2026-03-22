import Game.Metadata

World "BigOpAlgebra"
Level 7

Title "Filtering a Sum"

Introduction "
# Conditional Sums: sum_filter

Sometimes you want to sum only over elements satisfying a
predicate. `Finset.filter p s` gives the subset of `s` where `p`
holds. The theorem `sum_filter` relates the two views:

$$\\sum_{x \\in s,\\, p(x)} f(x) = \\sum_{x \\in s} \\begin{cases} f(x) & \\text{if } p(x) \\\\ 0 & \\text{otherwise} \\end{cases}$$

In Lean:
```
Finset.sum_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
  ∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0
```

This converts between two equivalent representations:
- **Filtered finset**: `∑ x ∈ s.filter p, f x` (sum over a smaller set)
- **If-then-else**: `∑ x ∈ s, if p x then f x else 0` (sum with a guard)

**The partition principle**: For any predicate `p`, every finset
`s` splits into `s.filter p` (where `p` holds) and
`s.filter (fun x => ¬ p x)` (where `p` fails). These two pieces
are disjoint and cover all of `s`. This means any sum over `s`
can be split into two parts using `sum_union` on these pieces.
`sum_filter` gives you a different angle on the same idea.

**Your task**: Given a known conditional sum, prove the
equivalent filtered-finset sum by converting between the two
representations.
"

/-- Convert an if-then-else sum to a filtered finset sum. -/
Statement (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ)
    (h : ∑ x ∈ s, (if p x then f x else 0) = 42) :
    ∑ x ∈ s.filter p, f x = 42 := by
  Hint "Use `rw [Finset.sum_filter]` to rewrite the filtered sum
  into an if-then-else sum over the full finset."
  rw [Finset.sum_filter]
  Hint "The goal now matches hypothesis `h`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`sum_filter` lets you convert freely between filtered-finset sums
and conditional sums. The choice depends on context:

- **Filtered finset** (`∑ x ∈ s.filter p, ...`): cleaner when you
  know exactly which elements contribute
- **If-then-else** (`∑ x ∈ s, if p x then ... else 0`): cleaner
  when you want to compute over the full finset

**Both directions**: This level used `rw [Finset.sum_filter]` to
rewrite the filtered sum into a conditional sum. The reverse
direction — `rw [← Finset.sum_filter]` — converts a conditional
sum back to a filtered-finset sum. Both directions are useful
depending on which representation your goal needs.

**The partition principle** gives a powerful proof strategy:
split any finset `s` into `s.filter p ∪ s.filter (¬p ·)`,
then reason about each piece. `sum_union` handles the sum
decomposition, and `sum_filter` handles the representation.
"

/-- `Finset.sum_filter` states that
`∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0`.

Converts between summing over a filtered finset and summing over
the full finset with an if-then-else guard.

## Syntax
```
rw [Finset.sum_filter]
exact Finset.sum_filter p f
```

## When to use it
When you want to convert between a sum over `s.filter p` and a
conditional sum over `s`, in either direction.
-/
TheoremDoc Finset.sum_filter as "Finset.sum_filter" in "BigOp"

NewTheorem Finset.sum_filter

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
