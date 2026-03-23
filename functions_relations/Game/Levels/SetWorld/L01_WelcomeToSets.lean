import Game.Metadata

World "SetWorld"
Level 1

Title "Welcome to Sets"

TheoremTab "Set"

Introduction "
# Welcome to Sets

In Lean 4, a **set** is not a primitive concept — it is built from
something you already know: **predicates**.

The definition is:
$$\\texttt{Set } \\alpha = \\alpha \\to \\texttt{Prop}$$

A set of natural numbers is just a function that takes a natural number
and returns a proposition. If the proposition is true, the number is
*in* the set; if false, it is *not* in the set.

**Membership** `x ∈ s` means: apply the predicate `s` to `x` and check
whether the result holds. So `x ∈ s` is just `s x` — function application!

The simplest set is `Set.univ`, the **universal set**. Its predicate is
`fun _ => True` — it returns `True` for every input. So `x ∈ Set.univ`
reduces to just `True`.

Look at your goal. The problem asks you to prove `x ∈ Set.univ`, but
the goal state shows `True` — because Lean has already evaluated the
membership predicate for you. All you need to do is prove `True`.

**Your task**: Use `constructor` to close the goal. (Recall that `True`
is a type with exactly one constructor, `True.intro`, and `constructor`
applies it.)
"

/-- Every element belongs to `Set.univ`. -/
Statement (x : ℕ) : x ∈ (Set.univ : Set ℕ) := by
  Hint "The goal is `True` because `x ∈ Set.univ` unfolds to `True`.
  Use `constructor` to prove it."
  Hint (hidden := true) "`constructor` applies `True.intro` and closes
  the goal."
  constructor

Conclusion "
You proved `x ∈ Set.univ` by proving `True`. This worked because:

1. `Set.univ` is defined as `fun _ => True`
2. `x ∈ Set.univ` means `Set.univ x` = `(fun _ => True) x` = `True`
3. `constructor` proves `True` via `True.intro`

The key insight: **set membership is predicate evaluation**. There is
no special set-theoretic machinery — just function application and
propositions. This is how all sets work in Lean.

The library name for this fact is `Set.mem_univ`: for any `x`, `x ∈ Set.univ`
holds.
"

/-- `Set α` is the type of sets with elements of type `α`.

In Lean, `Set α` is defined as `α → Prop` — a set IS its membership
predicate. An element `x : α` belongs to `s : Set α` when `s x` is true.

## Key facts
- Sets are predicates, not collections
- `x ∈ s` means `s x` (function application)
- Two sets are equal when they have the same elements (`Set.ext`)

## Warning
`Set α` is not the same as a type `α`. A set is a *predicate on* a type.
`Set.univ : Set α` contains all elements of `α`, but it is still a term
of type `Set α`, not the type `α` itself.
-/
DefinitionDoc Set as "Set"

/-- `x ∈ s` (for `s : Set α`) means that the predicate `s` holds at `x`.

Since `Set α = α → Prop`, membership `x ∈ s` is just `s x` — applying
the predicate to the element.

## Syntax
```
x ∈ s      -- x is a member of s
x ∉ s      -- x is not a member of s (notation for ¬ (x ∈ s))
```

## Example
If `s = fun n => n < 5`, then `3 ∈ s` is `3 < 5`.
-/
DefinitionDoc Set.Mem as "Set.Mem"

/-- `Set.univ : Set α` is the universal set — the set containing every
element of type `α`.

It is defined as `fun _ => True`, so `x ∈ Set.univ` is always `True`.

## Example
`x ∈ (Set.univ : Set ℕ)` reduces to `True`.

## Related
`Set.mem_univ x` is the proof that `x ∈ Set.univ`.
-/
DefinitionDoc Set.univ as "Set.univ"

NewTactic omega exact rw intro cases constructor assumption «have» use rfl apply induction
NewDefinition Set Set.Mem Set.univ

/-- `Set.mem_univ x` proves `x ∈ Set.univ` for any `x`. -/
TheoremDoc Set.mem_univ as "Set.mem_univ" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_univ Set.mem_setOf_eq Set.mem_setOf
