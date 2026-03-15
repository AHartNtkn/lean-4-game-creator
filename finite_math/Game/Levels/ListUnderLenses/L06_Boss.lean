import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 6

Title "Boss: Three lenses, one truth"

Introduction
"
# Boss: The Complete Comparison

You have now examined `[1, 2, 1, 3]` through all three lenses and seen
how mapping transforms the data. Time to integrate everything into a
single proof.

## The three cardinalities

| Lens | Representation | Cardinality | What is counted |
|------|---------------|-------------|-----------------|
| List | `[1, 2, 1, 3]` | 4 | All entries, in order |
| Multiset | `{1, 2, 1, 3}` | 4 | All entries, unordered |
| Finset | `{1, 2, 3}` | 3 | Distinct entries only |

## Your task

Prove a five-part conjunction:
1. The list length equals the multiset cardinality (both 4).
2. Reordering the list does not change the multiset.
3. The finset has cardinality 3.
4. The finset cardinality is at most the multiset cardinality
   (using the general theorem `Multiset.toFinset_card_le`).
5. Mapping `(· + 10)` preserves the multiset cardinality
   (using `Multiset.card_map`).

Each part uses a technique from an earlier level:
- L01--L02: `rfl` for definitional equalities
- L04: `rw [Multiset.coe_eq_coe]; decide` for permutation
- L03: `decide` for finset computations
- L05: `rw [Multiset.card_map]` for map-cardinality
- W4 L11: `exact Multiset.toFinset_card_le _` for the general inequality

There is no new material here. This is pure integration.
"

/-- The list `[1, 2, 1, 3]` under all three lenses, with map and inequality. -/
Statement :
    ([1, 2, 1, 3] : List Nat).length =
      Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) ∧
    (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) =
      ↑([3, 1, 2, 1] : List Nat) ∧
    (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset.card = 3 ∧
    (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset.card ≤
      Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) ∧
    Multiset.card (Multiset.map (· + 10) (↑([1, 2, 1, 3] : List Nat) : Multiset Nat)) =
      Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) := by
  Hint "The goal is a five-part conjunction. Use `constructor` to split
  off the first part."
  constructor
  · Hint "The first goal asks: does the list length equal the multiset
    cardinality? Since `Multiset.card (↑l) = l.length` by definition,
    both sides are the same number. What tactic proves this?"
    Hint (hidden := true) "Try `rfl`. Both sides reduce to `4`."
    rfl
  · Hint "Use `constructor` to split the remaining parts."
    constructor
    · Hint "The goal is a multiset equality. You proved this in Level 4.
      What bridge lemma converts multiset equality to a permutation check?"
      Hint (hidden := true) "Use `rw [Multiset.coe_eq_coe]` then `decide`."
      rw [Multiset.coe_eq_coe]
      Hint "Now verify the permutation with `decide`."
      decide
    · Hint "Use `constructor` to split the next parts."
      constructor
      · Hint "The finset cardinality is a concrete computation. After
        `toFinset` removes the duplicate `1`, the finset has 3 distinct
        elements (1, 2, and 3)."
        Hint (hidden := true) "Try `decide`."
        decide
      · Hint "Use `constructor` to split the final two parts."
        constructor
        · Hint "The goal is an inequality: finset cardinality is at most
          the multiset cardinality. Instead of computing both sides, apply
          the general theorem `Multiset.toFinset_card_le`."
          Hint (hidden := true) "Use `exact Multiset.toFinset_card_le _`.
          The `_` lets Lean infer the multiset argument."
          exact Multiset.toFinset_card_le _
        · Hint "The final goal asks whether mapping `(· + 10)` preserves
          the cardinality. You proved this in Level 5 using `card_map`."
          Hint (hidden := true) "Use `rw [Multiset.card_map]`."
          rw [Multiset.card_map]

Conclusion
"
Congratulations on completing the Three Lenses world!

You proved five facts about `[1, 2, 1, 3]`, each requiring a different
proof technique:

1. **Length = card**: `rfl` (definitional equality)
2. **Reordering invariance**: `rw [coe_eq_coe]; decide` (reduce-then-compute)
3. **Finset cardinality**: `decide` (concrete evaluation)
4. **Card inequality**: `exact toFinset_card_le _` (general theorem application)
5. **Map preserves card**: `rw [card_map]` (reduce-then-compute with trivial finish)

## The hierarchy in one picture

```
List     [1, 2, 1, 3]     length = 4     ordered, with duplicates
            ↓ ↑                            (forget order)
Multiset {1, 2, 1, 3}     card   = 4     unordered, with duplicates
            ↓ toFinset                     (forget duplicates)
Finset   {1, 2, 3}         card   = 3     unordered, no duplicates
```

Each step discards information:
- `↑` forgets **order**: `[1, 2, 1, 3]` and `[3, 1, 2, 1]` become the same
- `toFinset` forgets **multiplicity**: the two copies of `1` become one
- `map` preserves **count**: 4 items in, 4 items out

## Transfer moment

**Why does |{1, 2, 3}| = 3 even though the list has 4 elements?**

Because the finset counts **distinct** elements, not total entries.
The list `[1, 2, 1, 3]` has four entries, but only three distinct values:
1, 2, and 3. The duplicate `1` contributes to the list length and multiset
cardinality, but not to the finset cardinality.

In everyday mathematics, when you write \"the set of values in the sequence
1, 2, 1, 3 is {1, 2, 3},\" you are implicitly applying `toFinset`. The
formal version makes the information loss explicit.

## What you learned in this world

| Concept | Level | Proof move |
|---------|-------|------------|
| List perspective | L01 | `rfl` (length), `decide` (membership) |
| Multiset perspective | L02 | `rfl` (card = length), `rw [mem_coe]; decide` |
| Finset perspective | L03 | `decide` (toFinset equality, card) |
| Permutation + finset invariance | L04 | `rw [coe_eq_coe]; decide` + `decide` |
| Map preserves card | L05 | `rw [card_map]` |
| Integration | L06 | All of the above + `exact toFinset_card_le _` |

## What comes next

You have now seen the list-multiset-finset hierarchy on a concrete
example. In the upcoming worlds, you will work directly with **finsets**:
constructing them, testing membership, and applying set operations like
union, intersection, and difference.
"

DisabledTactic trivial native_decide simp aesop simp_all
