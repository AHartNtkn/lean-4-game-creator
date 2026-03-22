import Game.Metadata

World "BigOpIntro"
Level 12

Title "The Abstraction Ladder Beneath"

Introduction "
# Finset.sum Sits on the Abstraction Ladder

Remember the abstraction ladder from the AbstractionLadder world?

```
List  →  Multiset  →  Finset
(ordered,    (unordered,   (unordered,
 duplicates)  duplicates)   no duplicates)
```

Big operators live at the **Finset** level — the top of the ladder.
But they are *defined* in terms of the layer below.

Specifically, `Finset.sum s f` is defined as:
```
(s.val.map f).sum
```

That is:
1. Take `s.val` — the underlying `Multiset` of the finset
2. `Multiset.map f` — map `f` over it, producing a `Multiset` of values
3. `.sum` — sum the resulting `Multiset`

The `Multiset.sum` in turn uses `List.sum` on any representative
list. The Multiset layer guarantees the result doesn't depend on
which representative list you pick — that's what 'order doesn't
matter for addition' buys you.

**Your task**: Prove that `∑ x ∈ s, f x` equals `(s.val.map f).sum`.
This is definitionally true — the left side IS the right side by
definition.
"

/-- Finset.sum is defined via Multiset.map and Multiset.sum. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, f x = (Multiset.map f s.val).sum := by
  Hint "This is true by definition — `Finset.sum s f` is literally
  defined as `(s.val.map f).sum`. Use `rfl` to close it."
  rfl

Conclusion "
This was definitionally true — which is exactly the point. When you
write `∑ x ∈ s, f x`, Lean doesn't do anything magical. Under the
hood, it:

1. Looks up `s.val` — the `Multiset` underlying the `Finset`
2. Maps `f` over it: `Multiset.map f s.val`
3. Sums the result: `(Multiset.map f s.val).sum`

The **Multiset layer** is doing the real computational work. The
Finset layer adds the no-duplicates guarantee — which is why
`sum_insert` requires the `a ∉ s` hypothesis (to prevent
double-counting).

This is why the abstraction ladder matters: every big-operator
identity ultimately rests on multiset and list operations. The
three layers aren't just theoretically related — `Finset.sum` is
*literally built on top of* `Multiset.sum`.

This is the payoff of the **AbstractionLadder** world: the Multiset
layer exists precisely so that operations like summation are
well-defined regardless of element order. The `AddCommMonoid`
requirement on `∑` guarantees that `a + b = b + a`, which is
exactly what makes the multiset-level sum independent of which
representative list you pick.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
