import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 8

Title "Boss: Multi-step finset reasoning"

Introduction
"
# Boss: Multi-step finset reasoning

Time to integrate everything. Prove a three-part statement that
combines membership, set operations, subset reasoning, and
cardinality.

## Part 1: Membership after set difference

Prove that `7 ∈ {5, 7, 9, 11} \\ {9, 11, 13}`.

This requires showing `7 ∈ {5, 7, 9, 11}` **and** `7 ∉ {9, 11, 13}`.

## Part 2: A subset via intersection

Prove that `s ∩ t ⊆ s` for arbitrary finsets. This is the subset
proof pattern applied to a set-algebraic fact.

## Part 3: Union cardinality bound

Prove that for any finsets `s` and `t`:
```
(s ∪ t).card ≤ s.card + t.card
```

You proved this by induction in W10. Here you should apply the
**inclusion-exclusion lemma** directly and close with `omega`.

## Strategy

Use `refine ⟨?_, ?_, ?_⟩` to split, then handle each part with
the appropriate technique from Modules B--C.
"

/-- Multi-step finset reasoning combining membership, subset, and cardinality. -/
Statement {α : Type*} [DecidableEq α] (s t : Finset α) :
    (7 : Nat) ∈ ({5, 7, 9, 11} : Finset Nat) \ {9, 11, 13} ∧
    s ∩ t ⊆ s ∧
    (s ∪ t).card ≤ s.card + t.card := by
  Hint (hidden := true) "Use `refine ⟨?_, ?_, ?_⟩` to split into three goals."
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Membership in a set difference
    Hint (hidden := true) "Use `rw [Finset.mem_sdiff]` to split into
    membership and non-membership, then `constructor`."
    rw [Finset.mem_sdiff]
    constructor
    · simp [Finset.mem_insert, Finset.mem_singleton]
    · simp [Finset.mem_insert, Finset.mem_singleton]
  · -- Part 2: s ∩ t ⊆ s
    Hint (hidden := true) "Use `intro a ha`, then
    `rw [Finset.mem_inter] at ha` and extract `ha.1`."
    intro a ha
    rw [Finset.mem_inter] at ha
    exact ha.1
  · -- Part 3: Union cardinality bound
    Hint (hidden := true) "Use the inclusion-exclusion lemma to relate
    `(s ∪ t).card` to `s.card + t.card - (s ∩ t).card`.
    `have h := Finset.card_union_add_card_inter s t` gives
    `(s ∪ t).card + (s ∩ t).card = s.card + t.card`. Then `omega`."
    have h := Finset.card_union_add_card_inter s t
    omega

Conclusion
"
Congratulations on completing the Finset Reasoning problem set!

You proved a three-part statement integrating:

1. **Membership in a set difference** (V5 + `mem_sdiff`): showing an
   element is in one finset but not another.

2. **Subset via intersection** (V14 + `mem_inter`): the standard
   pattern of introducing an element and extracting from the
   hypothesis.

3. **Union cardinality bound** (M9 + inclusion-exclusion): using
   `card_union_add_card_inter` as a stepping stone, then `omega`.

## What you retrieved in this world

| Level | Skill | From world |
|-------|-------|-----------|
| L01 | Membership rewriting (V5) | W6 |
| L02 | Subset proofs (V14) | W7 |
| L03 | `ext` for set identity (V6, V7) | W7 |
| L04 | Filter + cardinality (M8, M9) | W8, W9 |
| L05 | Finset induction (V4) | W10 |
| L06 | Inclusion-exclusion (T4) | W9 |
| L07 | Subset-cardinality (T3) | W10 |
| L08 | Integration | All |

## Transfer moment

Every proof in this world has a direct paper counterpart:

- **Membership**: \"7 is in {5, 7, 9, 11} and not in {9, 11, 13},
  so 7 ∈ {5, 7, 9, 11} \\ {9, 11, 13}.\"

- **Intersection subset**: \"If x ∈ A ∩ B, then x ∈ A and x ∈ B,
  so in particular x ∈ A. Therefore A ∩ B ⊆ A.\"

- **Union bound**: \"By inclusion-exclusion,
  |A ∪ B| + |A ∩ B| = |A| + |B|. Since |A ∩ B| ≥ 0,
  we get |A ∪ B| ≤ |A| + |B|.\"

The Lean proofs and the paper proofs have the same logical structure.
The difference is only in notation and the level of explicitness
required.

## What comes next

The next world introduces **`Fintype`**: the type class that equips
a type with a universal finset `Finset.univ`, enabling type-level
counting via `Fintype.card`.
"

DisabledTactic trivial decide native_decide aesop simp_all
