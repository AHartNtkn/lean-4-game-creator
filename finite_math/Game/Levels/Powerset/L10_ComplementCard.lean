import Game.Metadata

World "Powerset"
Level 10

Title "Complement Cardinality"

Introduction "
# How Big Is the Complement?

In Level 9, you proved that the complement `s \\ t` is in the powerset
of `s`. Now let's count: how many elements does the complement have?

If `t` has `k` elements and `t ⊆ s`, then `s \\ t` has `s.card - t.card`
elements — you remove `k` elements from an `n`-element set, leaving
`n - k`.

This is the counting fact that makes the complement map work as a
bijection: it pairs each `k`-element subset with an `(n-k)`-element
subset. Without this cardinality result, the claim that 'choosing
`k` to include is the same as choosing `n-k` to exclude' is just
hand-waving.

**Your task**: Given `ht : t ∈ s.powerset`, prove
`(s \\ t).card = s.card - t.card`.

Strategy:
1. Extract `t ⊆ s` from powerset membership (Level 5 pattern)
2. Apply `Finset.card_sdiff_of_subset` — the cardinality of a set
   difference when the subtracted set is a subset
"

/-- `Finset.card_sdiff_of_subset` states that
`(s \\ t).card = s.card - t.card` when `t ⊆ s`.

## Syntax
```
exact Finset.card_sdiff_of_subset h
```
where `h : t ⊆ s`.

## When to use it
When the goal is `(s \\ t).card = s.card - t.card` and you know
`t ⊆ s`. Without the subset assumption, the identity does not hold
in the same form because `s ∩ t` might be smaller than `t`.

## Relationship to card_sdiff_add_card_inter
`card_sdiff_add_card_inter` works without a subset assumption but
gives `(s \\ t).card + (s ∩ t).card = s.card`. When `t ⊆ s`,
`s ∩ t = t`, so `card_sdiff_of_subset` is the cleaner version.
-/
TheoremDoc Finset.card_sdiff_of_subset as "Finset.card_sdiff_of_subset" in "Card"

/-- The complement of a subset has the expected cardinality. -/
Statement (s t : Finset ℕ) (ht : t ∈ s.powerset) :
    (s \ t).card = s.card - t.card := by
  Hint "Extract `t ⊆ s` from the powerset membership. This is the
  Level 5 pattern: rewrite `mem_powerset` in a hypothesis."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : t ⊆ s`. The goal is `(s \\ t).card = s.card - t.card`.
  The lemma `Finset.card_sdiff_of_subset` gives exactly this when the
  subtracted set is a subset."
  Hint (hidden := true) "Try `exact Finset.card_sdiff_of_subset ht`."
  exact Finset.card_sdiff_of_subset ht

Conclusion "
Two steps: `rw [mem_powerset] at ht` then `exact card_sdiff_of_subset ht`.

**Why this matters**: In Level 9, you proved that the complement
`s \\ t` is in the powerset. Now you know its size: if `t` has `k`
elements and `s` has `n` elements, then `s \\ t` has `n - k` elements.

This is the counting half of the complement bijection:
- Level 9: the complement map sends subsets to subsets
- This level: it sends `k`-element subsets to `(n-k)`-element subsets

Together, these two facts mean the complement map is a function from
`powersetCard k s` to `powersetCard (n-k) s`. The next level shows
it is its own inverse, completing the bijection.
"

NewTheorem Finset.card_sdiff_of_subset

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
