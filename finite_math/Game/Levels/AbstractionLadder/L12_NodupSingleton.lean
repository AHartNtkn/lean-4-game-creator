import Game.Metadata

World "AbstractionLadder"
Level 12

Title "Nodup: The Bridge to Finsets"

Introduction "
# From Lists to Finsets: The Nodup Condition

You know two layers now:
- `List α` — ordered, with duplicates
- `Multiset α` — unordered, with duplicates

The top layer, `Finset α`, requires **no duplicates**. How do we get
there?

The bridge is `List.Nodup`: a predicate asserting that a list has no
repeated elements.

`List.nodup_cons : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`

In words: `a :: l` has no duplicates if and only if `a` doesn't appear
in `l` AND `l` itself has no duplicates.

The base case: `List.nodup_nil : [].Nodup` — the empty list trivially
has no duplicates.

**Your task**: Prove that `[b]` (a singleton list) has no duplicates.

**Strategy**:
1. `rw [List.nodup_cons]` to split into `b ∉ [] ∧ [].Nodup`
2. Use `constructor` to split the conjunction
3. `List.not_mem_nil` closes `b ∉ []`
4. `List.nodup_nil` closes `[].Nodup`
"

/-- A singleton list has no duplicates. -/
Statement (b : ℕ) : List.Nodup [b] := by
  Hint "Start with `rw [List.nodup_cons]` to split the nodup condition.
  Remember: `[b]` is sugar for `b :: []`."
  rw [List.nodup_cons]
  Hint "The goal is `b ∉ [] ∧ [].Nodup`. Use `constructor` to split."
  constructor
  Hint "First goal: `b ∉ []`. Nothing belongs to the empty list."
  Hint (hidden := true) "Try `exact List.not_mem_nil`."
  · exact List.not_mem_nil
  Hint "Second goal: `[].Nodup`. The empty list trivially has no
  duplicates."
  Hint (hidden := true) "Try `exact List.nodup_nil`."
  · exact List.nodup_nil

Conclusion "
You proved a singleton list has no duplicates using the recursive
structure of `Nodup`:

1. `rw [List.nodup_cons]` — split `[b].Nodup` into `b ∉ [] ∧ [].Nodup`
2. `List.not_mem_nil` — nothing is in the empty list
3. `List.nodup_nil` — the empty list has no duplicates

These three tools — `nodup_cons`, `not_mem_nil`, and `nodup_nil` — are
the building blocks for proving ANY concrete list has no duplicates.
Next, you'll apply this pattern to a two-element list.

**Why nodup matters**: A `Finset α` is internally a pair `(val, nodup)`
where `val : Multiset α` and `nodup : val.Nodup`. The nodup condition
is what makes finsets reject duplicates. Every finset you've used so far
carries a hidden nodup proof.
"

/-- `List.Nodup l` asserts that list `l` has no duplicate elements.

## Key lemmas
- `List.nodup_nil : [].Nodup`
- `List.nodup_cons : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`
- `List.Nodup.cons : a ∉ l → l.Nodup → (a :: l).Nodup`
- `List.Perm.nodup_iff : l₁.Perm l₂ → (l₁.Nodup ↔ l₂.Nodup)`
-/
DefinitionDoc List.Nodup as "List.Nodup"

/-- `List.nodup_cons` states that
`(a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`.

## Syntax
```
rw [List.nodup_cons]
```

## When to use it
When proving or decomposing `Nodup` for a cons'd list.
-/
TheoremDoc List.nodup_cons as "List.nodup_cons" in "List"

/-- `List.nodup_nil` states that `[].Nodup`.

The empty list trivially has no duplicates.

## Syntax
```
exact List.nodup_nil
```
-/
TheoremDoc List.nodup_nil as "List.nodup_nil" in "List"

/-- `List.not_mem_nil` states that `a ∉ []`.

Nothing belongs to the empty list.

## Syntax
```
exact List.not_mem_nil
```
-/
TheoremDoc List.not_mem_nil as "List.not_mem_nil" in "List"

TheoremTab "List"
NewDefinition List.Nodup
NewTheorem List.nodup_cons List.nodup_nil List.not_mem_nil

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable List.nodup_singleton
