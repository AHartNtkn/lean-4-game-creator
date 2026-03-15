import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 9

Title "Boss: Cardinality of a union"

Introduction
"
# Boss: `card (s ∪ t) ≤ card s + card t`

Time to put everything together. You will prove the **subadditivity**
of cardinality: the cardinality of a union is at most the sum of the
individual cardinalities.

## Strategy: Finset induction on `s`

The proof goes by induction on `s`:

- **Base case** (`s = ∅`): `(∅ ∪ t).card ≤ 0 + t.card`.
  Use `Finset.empty_union` to simplify `∅ ∪ t = t`, then `omega`.

- **Inductive step**: Assume `(s' ∪ t).card ≤ s'.card + t.card`.
  Prove `(insert a s' ∪ t).card ≤ (insert a s').card + t.card`.

  The inductive step requires several moves:
  1. `Finset.insert_union`: rewrite `insert a s' ∪ t` as
     `insert a (s' ∪ t)`.
  2. `Finset.card_insert_le`: bound `(insert a (s' ∪ t)).card ≤
     (s' ∪ t).card + 1`.
  3. `Finset.card_insert_of_notMem ha`: compute
     `(insert a s').card = s'.card + 1`.
  4. Combine with the inductive hypothesis using `omega`.

## The proof skeleton

```
induction s using Finset.induction_on
case empty => ...
case insert a s' ha ih =>
  rw [Finset.insert_union]
  have h1 : ... := Finset.card_insert_le a (s' ∪ t)
  have h2 : ... := Finset.card_insert_of_notMem ha
  omega
```

## What you need

- `Finset.empty_union : ∅ ∪ s = s`
- `Finset.insert_union : insert a s ∪ t = insert a (s ∪ t)`
- `Finset.card_insert_le : (insert a s).card ≤ s.card + 1`
- `Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1`
- The inductive hypothesis `ih`
"

/-- The cardinality of a union is at most the sum of the cardinalities. -/
Statement {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∪ t).card ≤ s.card + t.card := by
  Hint "Start with `induction s using Finset.induction_on`."
  induction s using Finset.induction_on
  case empty =>
    Hint "The base case: `(∅ ∪ t).card ≤ (∅).card + t.card`.
    Use `rw [Finset.empty_union]` to simplify the left side, then `omega`."
    Hint (hidden := true) "Use `rw [Finset.empty_union]` then `omega`."
    rw [Finset.empty_union]
    omega
  case insert a s' ha ih =>
    Hint "The inductive step. You have:
    - `ha : a ∉ s'`
    - `ih : (s' ∪ t).card ≤ s'.card + t.card`

    First, rewrite the union using `rw [Finset.insert_union]` to get
    `insert a (s' ∪ t)` on the left side."
    rw [Finset.insert_union]
    Hint "Now use `have` to establish two intermediate facts:
    1. `(insert a (s' ∪ t)).card ≤ (s' ∪ t).card + 1`
       (from `Finset.card_insert_le`)
    2. `(insert a s').card = s'.card + 1`
       (from `Finset.card_insert_of_notMem ha`)"
    Hint (hidden := true) "Use:
    ```
    have h1 : (insert a (s' ∪ t)).card ≤ (s' ∪ t).card + 1 :=
      Finset.card_insert_le a (s' ∪ t)
    have h2 : (insert a s').card = s'.card + 1 :=
      Finset.card_insert_of_notMem ha
    omega
    ```"
    have h1 : (insert a (s' ∪ t)).card ≤ (s' ∪ t).card + 1 :=
      Finset.card_insert_le a (s' ∪ t)
    have h2 : (insert a s').card = s'.card + 1 :=
      Finset.card_insert_of_notMem ha
    omega

Conclusion
"
Congratulations on completing the Finset Induction world!

You proved `card_union_le`: the cardinality of a union is at most the
sum of the individual cardinalities. This required:

1. **Finset induction** on `s` (the new proof principle from this world)
2. **`insert_union`** to decompose the union at the insert boundary
3. **`card_insert_le`** to bound the cardinality increase (from L05)
4. **`card_insert_of_notMem`** with `ha : a ∉ s'` (the non-membership
   hypothesis that makes finset induction work)
5. **The inductive hypothesis** `ih` (combined via `omega`)

## What you learned in this world

| Level | Key lesson | Key lemma/move |
|-------|-----------|----------------|
| L01 | Nat induction review | `induction n with` |
| L02 | Finset induction intro | `induction s using Finset.induction_on` |
| L03 | Using `ha` for contradiction | `card_insert_of_notMem` at a hypothesis |
| L04 | Vacuous base case | `absurd` + `not_nonempty_empty` |
| L05 | `by_cases` on membership | `card_insert_of_mem`, `card_insert_of_notMem` |
| L06 | Subset card inequality | `card_le_card` |
| L07 | Nat vs Finset induction | Choose by parameter type |
| L08 | `refine` for induction | `refine Finset.induction_on s ?_ ?_` |
| L09 | Integration | All of the above |

## Transfer moment

In ordinary mathematics, the proof of `|A ∪ B| ≤ |A| + |B|` is almost
trivial: every element of `A ∪ B` is in `A` or `B` (or both), so
counting with multiplicity gives at most `|A| + |B|`.

The Lean proof is structurally different — it uses induction rather than
a counting argument — but the key insight is the same: insertion can
add at most one element, so the union cannot have more elements than
the combined count.

## What comes next

The next world is the **Finset Reasoning** problem set, where you
retrieve finset skills (membership, set operations, cardinality,
induction) under reduced scaffolding on fresh surface forms.
"

/-- `Finset.empty_union` states that `∅ ∪ s = s`.

The empty finset is the identity for union. -/
TheoremDoc Finset.empty_union as "Finset.empty_union" in "Finset"

NewTheorem Finset.empty_union Finset.card_insert_le
DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.card_union_le
