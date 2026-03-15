import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 14

Title "Boss: The full pipeline"

Introduction
"
# Boss: Integrating the hierarchy

Time to put everything together. You will work with two multisets and
prove facts that require the proof moves from this world -- not just
`decide` or `rfl`.

Consider the multiset `m₁ = ↑[0, 1, 0, 2]` (a multiset with a duplicate `0`)
and its image `m₂ = Multiset.map (· + 1) m₁` (the result of adding 1 to each
element).

## What you must prove

Three things:
1. Mapping preserves cardinality: `m₂.card = 4` (requires `card_map`)
2. The mapped multiset equals a specific list coercion:
   `m₂ = ↑[1, 2, 1, 3]` (requires `map_coe` + `coe_eq_coe` + `decide`)
3. The cardinality inequality: `m₂.toFinset.card ≤ m₂.card`
   (requires `toFinset_card_le`)

This boss integrates:
- `Multiset.card_map` (from L05)
- `Multiset.map_coe` + `Multiset.coe_eq_coe` (from L03, L13)
- `Multiset.toFinset_card_le` (from L11)
- `constructor` for splitting conjunctions

There is no new material -- only integration of skills from earlier levels.
"

/-- The full pipeline: map, compare, and bound cardinalities. -/
Statement :
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).card = 4 ∧
    Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat) = ↑([1, 2, 1, 3] : List Nat) ∧
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).toFinset.card ≤
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).card := by
  Hint "The goal is a three-part conjunction. Start by splitting the first
  conjunct with `constructor`."
  constructor
  · Hint "The goal involves the cardinality of a mapped multiset. You need to
    relate the cardinality of `Multiset.map f m` to the cardinality of `m`.
    What lemma says mapping preserves cardinality?"
    Hint (hidden := true) "Use `rw [Multiset.card_map]` to remove the `map`,
    leaving `(↑[0, 1, 0, 2]).card = 4`, which is `rfl`."
    rw [Multiset.card_map]
    rfl
  · Hint "Use `constructor` to split the remaining two parts."
    constructor
    · Hint "The goal is a multiset equality: `Multiset.map (· + 1) ↑[0, 1, 0, 2] = ↑[1, 2, 1, 3]`.
      Apply the reduce-then-compute pattern: first push the map inside the
      coercion, then reduce to a permutation."
      Hint (hidden := true) "Use `rw [Multiset.map_coe]` to convert the left
      side, then `rw [Multiset.coe_eq_coe]` to reduce to a permutation, then `decide`."
      rw [Multiset.map_coe]
      rw [Multiset.coe_eq_coe]
      decide
    · Hint "The goal is a cardinality inequality. What general theorem states
      that `m.toFinset.card ≤ m.card` for any multiset `m`?"
      Hint (hidden := true) "Use `exact Multiset.toFinset_card_le _`."
      exact Multiset.toFinset_card_le _

Conclusion
"
Congratulations on completing the Multisets and Hierarchy world!

You proved three facts about the mapped multiset, each requiring a
different proof technique from this world:

1. **Cardinality of mapped multiset**: `rw [Multiset.card_map]; rfl`
   -- the reduce-then-compute pattern (L05)
2. **Multiset equality via permutation**: `rw [map_coe, coe_eq_coe]; decide`
   -- the two-step reduction to permutation check (L03, L13)
3. **Cardinality inequality**: `exact toFinset_card_le _`
   -- applying a general theorem (L11)

Unlike a proof that uses only `decide`, this boss required you to
**choose the right lemma** at each step. That is the skill this world
teaches: knowing which bridge lemma to apply to reduce a multiset
question to a computable form.

## What you learned in this world

| Concept | Introduced | Proof move |
|---------|-----------|------------|
| `Multiset` | L01 | `rfl` for definitional equalities |
| `Multiset.mem_coe` | L02 | Reduce membership to list level |
| `Multiset.coe_eq_coe` | L03 | Reduce equality to permutation |
| Information loss (lists) | L04 | Conjunction: inequality + equality |
| `Multiset.map`, `card_map` | L05 | Remove map from cardinality |
| `Multiset.count` | L06 | Compute with `decide` |
| `count_cons_self/of_ne` | L07 | Symbolic counting |
| `Multiset.toFinset` | L08 | Deduplicate to finset |
| Information loss (finsets) | L09 | Different inputs, same finset |
| Three-layer hierarchy | L10 | Compare cardinalities |
| `toFinset_card_le` | L11 | General inequality |
| `Nodup`, `dedup`, `coe_nodup` | L12 | Connect W3 and W4 |
| Reduce-then-compute | L13 | Named proof strategy |

## Transfer to paper proofs

In ordinary mathematics, when you say \"the set of elements in the list\" or
\"the set $\\{a_1, \\ldots, a_n\\}$ where the $a_i$ may have repetitions,\" you
are implicitly applying `toFinset`. In Lean, this operation is explicit, and
it reminds you that information (order and multiplicity) is being discarded.

The **reduce-then-compute** pattern transfers directly to mathematical
writing: \"By [theorem name], this reduces to [simpler statement], which
holds by [direct verification].\" The bridge lemma is the theorem citation;
the computation is the verification.

## What comes next

In the next world, you will work directly with **finsets** -- learning
how to construct them, test membership, and apply set operations.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
