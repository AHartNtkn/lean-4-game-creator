import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 10

Title "Boss: De Morgan's law for finsets"

Introduction
"
# Boss: De Morgan's law for finite sets

Time to integrate everything from this world. You will prove
**De Morgan's law for finsets**:

```
s \\ (t ∩ u) = (s \\ t) ∪ (s \\ u)
```

This says: the elements of `s` that are **not** in `t ∩ u` are exactly
those that are not in `t` **or** not in `u`.

## Proof plan

1. Use `ext a` to reduce to membership.
2. Use `constructor` to split the biconditional.
3. **Forward**: From `a ∈ s \\ (t ∩ u)`, extract `a ∈ s` and
   `a ∉ t ∩ u`. Use the fact that `a ∉ t ∩ u` means it is not the
   case that `a ∈ t` **and** `a ∈ u`. Use `by_cases` on `a ∈ t` to
   determine which side of `(s \\ t) ∪ (s \\ u)` receives `a`.
4. **Reverse**: From `a ∈ (s \\ t) ∪ (s \\ u)`, case-split on
   which part of the union `a` came from, and in each case show
   `a ∈ s \\ (t ∩ u)`.

This proof uses every major tool from this world: `ext`, `mem_union`,
`mem_inter`, `mem_sdiff`, `by_cases`, `rcases`, and `constructor`.
"

/-- De Morgan's law for finsets: `s \\ (t ∩ u) = (s \\ t) ∪ (s \\ u)`. -/
Statement (s t u : Finset Nat) :
    s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by
  Hint "Start with `ext a` to reduce to a membership biconditional."
  Hint (hidden := true) "Use `ext a`."
  ext a
  Hint "Split the biconditional."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · -- Forward: a ∈ s \ (t ∩ u) → a ∈ (s \ t) ∪ (s \ u)
    Hint "Introduce the hypothesis and expand the set difference."
    Hint (hidden := true) "Use `intro h`, then
    `rw [Finset.mem_sdiff] at h`."
    intro h
    rw [Finset.mem_sdiff] at h
    Hint "Extract the two parts: `a ∈ s` and `a ∉ t ∩ u`."
    Hint (hidden := true) "Use `rcases h with ⟨hs, hntu⟩`."
    rcases h with ⟨hs, hntu⟩
    Hint "You have `hs : a ∈ s` and `hntu : a ∉ t ∩ u`. The key
    question is: is `a ∈ t` or not? Use `by_cases` to split."
    Hint (hidden := true) "Use `by_cases ht : a ∈ t`."
    by_cases ht : a ∈ t
    · Hint "**Case `ht : a ∈ t`**: Since `a ∉ t ∩ u` but `a ∈ t`, we
      must have `a ∉ u`. (If `a` were in `u`, then `a ∈ t ∩ u`,
      contradicting `hntu`.) So `a ∈ s \\ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, `right`,
      `rw [Finset.mem_sdiff]`, then build the pair. For the second
      component, use `intro hu` then `apply hntu` then
      `rw [Finset.mem_inter]` then `exact ⟨ht, hu⟩`."
      rw [Finset.mem_union]
      right
      rw [Finset.mem_sdiff]
      constructor
      · exact hs
      · intro hu
        apply hntu
        rw [Finset.mem_inter]
        exact ⟨ht, hu⟩
    · Hint "**Case `ht : a ∉ t`**: Since `a ∈ s` and `a ∉ t`, we have
      `a ∈ s \\ t`. So `a` goes in the left side of the union."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, `left`,
      `rw [Finset.mem_sdiff]`, `exact ⟨hs, ht⟩`."
      rw [Finset.mem_union]
      left
      rw [Finset.mem_sdiff]
      exact ⟨hs, ht⟩
  · -- Reverse: a ∈ (s \ t) ∪ (s \ u) → a ∈ s \ (t ∩ u)
    Hint "Introduce the hypothesis and expand the union."
    Hint (hidden := true) "Use `intro h`, then
    `rw [Finset.mem_union] at h`."
    intro h
    rw [Finset.mem_union] at h
    Hint "Case-split on which part of the union `a` came from."
    Hint (hidden := true) "Use `rcases h with hst | hsu`."
    rcases h with hst | hsu
    · Hint "Case `hst : a ∈ s \\ t`. Extract `a ∈ s` and `a ∉ t`."
      Hint (hidden := true) "Use `rw [Finset.mem_sdiff] at hst`,
      `rcases hst with ⟨hs, hnt⟩`."
      rw [Finset.mem_sdiff] at hst
      rcases hst with ⟨hs, hnt⟩
      Hint "Show `a ∈ s \\ (t ∩ u)`. You need `a ∈ s` (which you have)
      and `a ∉ t ∩ u`. Since `a ∉ t`, certainly `a ∉ t ∩ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_sdiff]`, `constructor`,
      `exact hs`, then for the non-membership: `intro htu`,
      `rw [Finset.mem_inter] at htu`, `rcases htu with ⟨ht, _⟩`,
      `exact hnt ht`."
      rw [Finset.mem_sdiff]
      constructor
      · exact hs
      · intro htu
        rw [Finset.mem_inter] at htu
        rcases htu with ⟨ht, _⟩
        exact hnt ht
    · Hint "Case `hsu : a ∈ s \\ u`. Extract `a ∈ s` and `a ∉ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_sdiff] at hsu`,
      `rcases hsu with ⟨hs, hnu⟩`."
      rw [Finset.mem_sdiff] at hsu
      rcases hsu with ⟨hs, hnu⟩
      Hint "Show `a ∈ s \\ (t ∩ u)`. Since `a ∉ u`, certainly
      `a ∉ t ∩ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_sdiff]`, `constructor`,
      `exact hs`, then `intro htu`, `rw [Finset.mem_inter] at htu`,
      `rcases htu with ⟨_, hu⟩`, `exact hnu hu`."
      rw [Finset.mem_sdiff]
      constructor
      · exact hs
      · intro htu
        rw [Finset.mem_inter] at htu
        rcases htu with ⟨_, hu⟩
        exact hnu hu

Conclusion
"
Congratulations on completing the Finset Operations world!

You proved **De Morgan's law for finsets**:
`s \\ (t ∩ u) = (s \\ t) ∪ (s \\ u)`.

This proof integrated every major technique from the world:

- **`ext`** to reduce finset equality to membership (L05-L06)
- **`mem_union`** for union membership (L01)
- **`mem_inter`** for intersection membership (L02)
- **`mem_sdiff`** for set difference membership (L03)
- **`by_cases`** for case analysis on membership (L08)
- **`rcases`** for destructuring conjunctions and disjunctions (from W6)
- **Negation reasoning**: proving `a ∉ t ∩ u` by assuming `a ∈ t ∩ u`
  and deriving a contradiction

## Transfer to ordinary mathematics

De Morgan's law for sets is a standard exercise in any foundations
course. The proof you just wrote is **exactly** the paper proof:

> \"To show s \\ (t ∩ u) = (s \\ t) ∪ (s \\ u), take an arbitrary
> element a.
>
> (→) If a ∈ s \\ (t ∩ u), then a ∈ s and a ∉ t ∩ u.
> Either a ∉ t (then a ∈ s \\ t) or a ∈ t (then since a ∉ t ∩ u,
> we have a ∉ u, so a ∈ s \\ u). In either case, a ∈ (s \\ t) ∪ (s \\ u).
>
> (←) If a ∈ (s \\ t) ∪ (s \\ u), then either a ∈ s \\ t or
> a ∈ s \\ u. In the first case, a ∈ s and a ∉ t, so a ∉ t ∩ u.
> In the second, a ∈ s and a ∉ u, so again a ∉ t ∩ u. Either way,
> a ∈ s \\ (t ∩ u). □\"

The Lean proof and the paper proof have the same structure. The only
difference is that Lean requires you to be explicit about every step.

## What you learned in this world

- **`Finset.mem_union`** -- union membership as disjunction (L01)
- **`Finset.mem_inter`** -- intersection membership as conjunction (L02)
- **`Finset.mem_sdiff`** -- set difference as conjunction with negation (L03)
- **Combining operations** -- outermost operation determines proof shape (L04)
- **`ext`** -- proving finset equality via membership (L05-L06)
- **Subset proofs** via `intro a ha` (L07)
- **`by_cases`** -- case analysis on decidable propositions (L08)
- **Complex `ext` proofs** combining multiple membership lemmas (L09-L10)

## What comes next

In the next world, you will learn to **filter** finsets by predicates,
**map** functions over finsets, and reason about membership in the
resulting finsets.
"

DisabledTactic trivial decide native_decide aesop simp_all
