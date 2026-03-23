import Game.Metadata

World "CountingTechniques"
Level 6

Title "Strict Subset Means Strictly Fewer"

Introduction "
# Strict Subsets and Strict Inequalities

You know that `s ⊆ t` implies `s.card ≤ t.card`
(`Finset.card_le_card`). But what about *strict* subsets?

A **strict subset** `s ⊂ t` (typed `\\ssubset` or `\\sub`) means
`s ⊆ t` AND `s ≠ t` — everything in `s` is in `t`, but `t`
has something extra. The theorem `Finset.card_lt_card` captures
the cardinality consequence:

```
Finset.card_lt_card : s ⊂ t → s.card < t.card
```

**Building a strict subset**: You often don't have `s ⊂ t` directly.
You have `s ⊆ t` (a subset relation) and evidence that some element
is in `t` but not in `s`. The bridge is `Finset.ssubset_iff_of_subset`:

```
Finset.ssubset_iff_of_subset :
  s ⊆ t → (s ⊂ t ↔ ∃ x ∈ t, x ∉ s)
```

**Your task**: Given `s ⊆ t`, an element `a ∈ t` with `a ∉ s`,
prove `s.card < t.card`.
"

/-- A subset missing an element is strictly smaller. -/
Statement (s t : Finset ℕ) (hsub : s ⊆ t) (a : ℕ)
    (hat : a ∈ t) (has : a ∉ s) :
    s.card < t.card := by
  Hint "You need to show `s ⊂ t` (strict subset), then apply
  `Finset.card_lt_card`. First build the strict subset using
  `Finset.ssubset_iff_of_subset`."
  Hint (hidden := true) "Start with
  `apply Finset.card_lt_card`."
  apply Finset.card_lt_card
  Hint "The goal is now `s ⊂ t`. Use `ssubset_iff_of_subset` to
  convert this: since you already have `hsub : s ⊆ t`, you just
  need to exhibit an element in `t` but not in `s`."
  Hint (hidden := true) "Try `rw [Finset.ssubset_iff_of_subset hsub]`."
  rw [Finset.ssubset_iff_of_subset hsub]
  Hint "The goal is `∃ x ∈ t, x ∉ s`. Provide the witness `a`."
  Hint (hidden := true) "Try `exact ⟨a, hat, has⟩`."
  exact ⟨a, hat, has⟩

Conclusion "
The strict subset → strict inequality pattern:
1. `apply Finset.card_lt_card` — reduce to proving `s ⊂ t`
2. `rw [Finset.ssubset_iff_of_subset hsub]` — with `s ⊆ t`
   known, reduce to finding a witness
3. `exact ⟨a, hat, has⟩` — provide the missing element

**When to reach for `card_lt_card`**: Whenever you need `<`
instead of `≤`. The key is identifying something in `t` that
can't be in `s`. Combined with `card_le_card` (for `≤`), you
have complete control over cardinality comparisons from subset
relations.

**Warning — the converse is false**: `s.card < t.card` does
**not** imply `s ⊂ t`. Consider `s = {1, 2}` and `t = {3, 4, 5}`:
we have `s.card = 2 < 3 = t.card`, but `s` is not a subset of `t`
at all (they're disjoint). Cardinality measures *size*, not
*containment*. You need the structural condition `s ⊂ t`, not
just a size comparison.

**Connection to injection bounds**: A strict subset `s ⊂ t`
induces a natural injection from `s` to `t` (the inclusion map)
that is *not* surjective — the missing element `a` witnesses the
failure of surjectivity. So `card_lt_card` can be seen as a
consequence of Level 2's injection bound plus the extra information
that the injection misses something. The next level makes this
connection precise: injection + non-surjectivity implies strict
inequality.

**Looking ahead**: `card_lt_card` and `ssubset_iff_of_subset` are
supporting tools that you'll use in PsetCounting when solving
problems involving subset cardinality comparisons.
"

/-- `Finset.card_lt_card h` states that `s ⊂ t` implies
`s.card < t.card`.

## Syntax
```
apply Finset.card_lt_card
-- then prove s ⊂ t
```
or
```
have h := Finset.card_lt_card hssubset
```

## When to use it
When you have a strict subset `s ⊂ t` and need `s.card < t.card`.
Often combined with `ssubset_iff_of_subset` to build the strict
subset from a regular subset plus a witness.
-/
TheoremDoc Finset.card_lt_card as "Finset.card_lt_card" in "Card"

/-- `Finset.ssubset_iff_of_subset hsub` states that when
`hsub : s ⊆ t`, we have `s ⊂ t ↔ ∃ x ∈ t, x ∉ s`.

## Syntax
```
rw [Finset.ssubset_iff_of_subset hsub]
```

## When to use it
When you have `s ⊆ t` and want to prove `s ⊂ t` by exhibiting
an element in `t` that's not in `s`.
-/
TheoremDoc Finset.ssubset_iff_of_subset as "Finset.ssubset_iff_of_subset" in "Card"

NewTheorem Finset.card_lt_card Finset.ssubset_iff_of_subset

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
