import Game.Metadata

World "Cardinality"
Level 15

Title "Disjoint Union"

Introduction "
# When the Overlap Is Empty

Continue using the 'collect card facts, then omega' strategy.

Two finsets are **disjoint** when they share no elements:
$s \\cap t = \\emptyset$. In this case, inclusion-exclusion simplifies:

$$|s \\cup t| = |s| + |t|$$

(since $|s \\cap t| = 0$, the correction term vanishes).

**Concrete example**: Consider the even numbers $\\{2, 4, 6\\}$ and the
odd numbers $\\{1, 3, 5\\}$ from the range 1 to 6. These sets share no
elements — every number is either even or odd, not both. So
$|\\{2,4,6\\} \\cup \\{1,3,5\\}| = 3 + 3 = 6$. No overlap correction needed.

In general, disjointness arises whenever sets are constructed to partition
a space — splitting by a predicate (even/odd, positive/negative),
taking $s \\setminus t$ and $s \\cap t$ from Level 16, or using complementary
filters.

In Lean:
```
Finset.card_union_of_disjoint : Disjoint s t → (s ∪ t).card = s.card + t.card
```

`Disjoint s t` is Lean's way of saying the two sets share no elements.

**Your task**: Given disjoint sets of known sizes, compute the size of
their union.
"

/-- The union of disjoint sets has cardinality equal to the sum. -/
Statement (s t : Finset ℕ) (h : Disjoint s t)
    (hs : s.card = 4) (ht : t.card = 6) :
    (s ∪ t).card = 10 := by
  Hint "Apply `Finset.card_union_of_disjoint h` to get the
  simplified equation, then use `omega`."
  Hint (hidden := true) "Try
  `have hd := Finset.card_union_of_disjoint h` and then `omega`."
  have hd := Finset.card_union_of_disjoint h
  omega

Conclusion "
`card_union_of_disjoint` is the special case of inclusion-exclusion
when the overlap is empty. It's cleaner and more direct.

In practice, you'll use this lemma when you can prove the sets are
disjoint — often because they were constructed to be disjoint
(e.g., `s \\ t` is always disjoint from `s ∩ t`).

Comparison:
- `card_union_add_card_inter`: always applies, but gives an equation
  with four terms
- `card_union_of_disjoint`: requires disjointness, but gives a
  simpler equation with three terms
"

/-- `Finset.card_union_of_disjoint h` states that when `h : Disjoint s t`,
`(s ∪ t).card = s.card + t.card`.

## Syntax
```
have hd := Finset.card_union_of_disjoint h
```

## When to use it
When `s` and `t` are known to be disjoint and you need the cardinality
of their union.

## Where disjointness comes from
Common sources of `Disjoint s t`:
- `sdiff_disjoint : Disjoint (s \\ t) t`
- Explicitly constructed disjoint partitions
- `Finset.disjoint_filter_filter` for complementary predicates
-/
TheoremDoc Finset.card_union_of_disjoint as "Finset.card_union_of_disjoint" in "Card"

/-- `Disjoint s t` means that `s` and `t` share no elements.

For finsets, `Disjoint s t` is equivalent to `s ∩ t = ∅`.

## When you see it
`Disjoint s t` appears as a hypothesis in lemmas like
`card_union_of_disjoint` that give simplified counting formulas
when two sets don't overlap.
-/
DefinitionDoc Disjoint as "Disjoint"

TheoremTab "Card"
NewTheorem Finset.card_union_of_disjoint
NewDefinition Disjoint

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
