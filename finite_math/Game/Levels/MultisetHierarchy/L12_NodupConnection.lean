import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 12

Title "Nodup and the W3 connection"

Introduction
"
# The bridge between List.Nodup and Multiset.Nodup

In the Lists world (W3), you learned about `List.Nodup`: the property
that every element appears at most once. Now you will see its multiset
counterpart.

## `Multiset.Nodup`

`Multiset.Nodup m` asserts that every element of multiset `m` has
multiplicity at most 1 -- no duplicates.

## `Multiset.coe_nodup`

The key connection is:

```
Multiset.coe_nodup : (↑l : Multiset α).Nodup ↔ l.Nodup
```

A coerced list has no duplicate elements as a multiset if and only if it
has no duplicate elements as a list. This makes sense: coercion only
forgets order, and `Nodup` does not depend on order.

## `Multiset.dedup`

`Multiset.dedup m` removes duplicate elements from a multiset, keeping
one copy of each distinct element. It is the internal mechanism behind
`Multiset.toFinset`.

## `Multiset.toFinset_val`

The relationship between `toFinset` and `dedup` is:

```
Multiset.toFinset_val : (Multiset.toFinset m).val = Multiset.dedup m
```

A `Finset` is defined as `{ val : Multiset α // val.Nodup }`. The `.val`
field extracts the underlying multiset. So `toFinset_val` says: the
underlying multiset of `toFinset m` is `dedup m`.

## Your task

Prove two things:
1. The list `[1, 2, 3]` has `Nodup` as a multiset (connecting back to W3)
2. The underlying multiset of `toFinset ↑[1, 2, 1, 3]` is `dedup ↑[1, 2, 1, 3]`

For part 1, rewrite with `Multiset.coe_nodup` to reduce to `List.Nodup`,
then use `decide`.

For part 2, use `exact Multiset.toFinset_val _`.
"

/-- List.Nodup lifts to Multiset.Nodup, and toFinset uses dedup internally. -/
Statement : (↑([1, 2, 3] : List Nat) : Multiset Nat).Nodup ∧
    (Multiset.toFinset (↑([1, 2, 1, 3] : List Nat) : Multiset Nat)).val =
    Multiset.dedup (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) := by
  Hint "The goal is a conjunction. Split it with `constructor`."
  constructor
  · Hint "The first goal asks whether the multiset `↑[1, 2, 3]` has no duplicates.
    This is a question about `Multiset.Nodup`. You know from W3 that the list
    `[1, 2, 3]` has no duplicates. What lemma connects `Multiset.Nodup` to `List.Nodup`?"
    Hint (hidden := true) "Use `rw [Multiset.coe_nodup]` to convert the multiset
    `Nodup` to a list `Nodup`, then `decide`."
    rw [Multiset.coe_nodup]
    Hint "Now the goal is `[1, 2, 3].Nodup`. This is a concrete property of a
    specific list. Try `decide`."
    decide
  · Hint "The second goal asks about the internal structure of `toFinset`. What
    lemma relates `.val` of a `toFinset` to `dedup`?"
    Hint (hidden := true) "Use `exact Multiset.toFinset_val _`. The `_` tells Lean
    to infer the multiset argument."
    exact Multiset.toFinset_val _

Conclusion
"
You connected two worlds:

**Part 1** showed that `List.Nodup` and `Multiset.Nodup` are the same
condition, just expressed at different levels of the hierarchy. If a list
has no duplicates, then its multiset also has no duplicates (and vice versa).
This is because `Nodup` only cares about *which elements appear how many
times*, not about their *order* -- and order is the only thing forgotten
by the coercion.

**Part 2** revealed the internal mechanism of `toFinset`:
1. `dedup` removes duplicates from the multiset, producing a `Nodup` multiset
2. `toFinset` bundles this `Nodup` multiset into a `Finset`
3. `.val` extracts the underlying multiset from the `Finset`

So `(toFinset m).val = dedup m` -- the finset's underlying data is the
deduplicated multiset.

**The full hierarchy in Lean types**:
```
List α  ──↑──>  Multiset α  ──toFinset──>  Finset α
              (= Quot List.Perm)         (= {m : Multiset α // m.Nodup})
```

- Step 1 forgets order (quotienting by permutations)
- Step 2 forgets multiplicity (deduplicating, then bundling with `Nodup`)

**In plain language**: \"To get a set from a bag, remove the duplicates.
The result is a bag where every item appears exactly once -- which is
exactly what a set is.\"
"

/-- `Multiset.Nodup m` asserts that every element of `m` has multiplicity at most 1.
It is the multiset analogue of `List.Nodup`. A `Finset` is internally a multiset
satisfying `Nodup`. -/
DefinitionDoc Multiset.Nodup as "Multiset.Nodup"

/-- `Multiset.dedup m` removes duplicate elements from multiset `m`, keeping one
copy of each distinct element. The result satisfies `Multiset.Nodup`.
`Multiset.toFinset` uses `dedup` internally. -/
DefinitionDoc Multiset.dedup as "Multiset.dedup"

/-- `Multiset.coe_nodup` states that `(↑l : Multiset α).Nodup ↔ l.Nodup`.
A coerced list has no multiset duplicates iff the list itself has no duplicates.
Use `rw [Multiset.coe_nodup]` to convert between the two forms. -/
TheoremDoc Multiset.coe_nodup as "Multiset.coe_nodup" in "Multiset"

/-- `Multiset.toFinset_val` states that `(Multiset.toFinset m).val = Multiset.dedup m`.
The underlying multiset of a finset obtained by `toFinset` is the deduplicated
version of the original multiset. -/
TheoremDoc Multiset.toFinset_val as "Multiset.toFinset_val" in "Multiset"

NewDefinition Multiset.Nodup Multiset.dedup
NewTheorem Multiset.coe_nodup Multiset.toFinset_val
DisabledTactic trivial native_decide simp aesop simp_all
