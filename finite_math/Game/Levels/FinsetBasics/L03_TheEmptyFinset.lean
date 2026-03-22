import Game.Metadata

World "FinsetBasics"
Level 3

Title "The Empty Finset"

Introduction "
# The Empty Finset

The empty finset `∅ : Finset α` contains no elements.

This is captured by the theorem `Finset.notMem_empty`:
$$\\forall a, \\; a \\notin \\varnothing$$

In other words, no element is a member of the empty set.

`Finset.notMem_empty` is a *function*: give it an element `a`, and it
returns a proof that `a ∉ ∅`. So `Finset.notMem_empty x` is a proof
of `x ∉ ∅`.

**Your task**: Prove that no natural number is in the empty finset.

After `intro x`, the goal becomes `x ∉ ∅`. Close it with
`exact Finset.notMem_empty x`.
"

/-- No natural number is a member of the empty finset. -/
Statement : ∀ x : ℕ, x ∉ (∅ : Finset ℕ) := by
  Hint "The goal is universally quantified. Start with `intro x`."
  intro x
  Hint "The goal is `x ∉ ∅`. This is a direct consequence of a theorem
  about the empty finset — no element can belong to it. Look for a
  theorem in your inventory that says exactly this."
  Hint (hidden := true) "Use `exact Finset.notMem_empty x`."
  exact Finset.notMem_empty x

Conclusion "
The empty set is the simplest case: nothing is in it.

`Finset.notMem_empty a` directly produces a proof of `a ∉ ∅`.
This is a *term-mode* proof — you hand `exact` a complete proof term
rather than building the proof step by step with tactics.

In ordinary set theory, $\\varnothing$ having no elements is an axiom.
In Lean's `Finset`, it follows from the construction: the empty finset
has an empty underlying list, so membership lookup always fails.

You'll use `Finset.notMem_empty` less often than you might expect —
most non-membership proofs involve *non-empty* sets, and those require
a different technique (coming in Level 6).
"

/-- `Finset.notMem_empty a` proves `a ∉ ∅`.

No element is a member of the empty finset.

## Syntax
```
exact Finset.notMem_empty x
```

## When to use it
When the goal is `x ∉ ∅` (or equivalently `¬ (x ∈ ∅)`).

## Example
```
-- Goal: x ∉ ∅
exact Finset.notMem_empty x
```
-/
TheoremDoc Finset.notMem_empty as "Finset.notMem_empty" in "Finset"

/-- `∅ : Finset α` is the empty finset, containing no elements.

## Notation
`∅` is notation for `Finset.empty`.

## Key property
No element belongs to the empty finset: `Finset.notMem_empty a : a ∉ ∅`

## When you encounter it
The empty finset is the base case for induction on finsets,
and `Finset.range 0 = ∅` (the range with zero elements).
-/
DefinitionDoc Finset.empty as "Finset.empty"

NewDefinition Finset.empty
NewTheorem Finset.notMem_empty

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
