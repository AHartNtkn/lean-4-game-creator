import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 5

Title "Finset.cons and the proof obligation"

Introduction
"
# `Finset.cons` vs `insert`

You have been using `insert` to build finsets. There is a second way to
add an element: `Finset.cons`.

## The difference

- **`insert a s`**: adds `a` to `s`. If `a ∈ s`, nothing changes.
  No proof obligation -- it handles duplicates silently.
- **`Finset.cons a s h`**: adds `a` to `s`, but requires a proof
  `h : a ∉ s`. The caller must guarantee that `a` is not already in `s`.

Why would you ever use `cons` when `insert` is easier? Because `cons`
carries more information: the proof `h : a ∉ s` tells Lean (and future
proof steps) that `a` is genuinely new. Some lemmas have simpler
statements when using `cons` instead of `insert`, because the
non-membership is already known.

## Your task

Prove that the finset built with `cons` equals the one built with `insert`.
Specifically, given a proof `h` that `1 ∉ {2}`, prove
`Finset.cons 1 {2} h = {1, 2}`.

The lemma `Finset.cons_eq_insert` states:
```
Finset.cons_eq_insert a s h : Finset.cons a s h = insert a s
```
"

/-- Building `{1, 2}` with `cons` gives the same result as with `insert`. -/
Statement (h : (1 : Nat) ∉ ({2} : Finset Nat)) :
    Finset.cons 1 {2} h = {1, 2} := by
  Hint "You need to show that `Finset.cons 1 ...` equals the literal
  finset. There is a lemma that converts `cons` to `insert`. What is it?"
  Hint (hidden := true) "Use `rw [Finset.cons_eq_insert]`. This rewrites
  `Finset.cons a s h` to `insert a s`, and the result matches by `rfl`."
  rw [Finset.cons_eq_insert]

Conclusion
"
`Finset.cons` and `insert` produce the same finset when the element is
genuinely new. The difference is in the **type signature**:

- `insert a s` always works, but may silently do nothing if `a ∈ s`.
- `Finset.cons a s h` requires a proof `h : a ∉ s`, guaranteeing the
  element is new.

## When to use which

In practice:
- Use **`insert`** (and `{a, b, c}` notation) for constructing finsets
  in statements and everyday proofs. It is simpler and more convenient.
- Use **`Finset.cons`** when you need the non-membership proof for a
  subsequent argument -- for example, in induction on finsets where you
  add one element at a time and need to know it was not already there.

The bridge lemma `Finset.cons_eq_insert` lets you move between the two.

**In plain language**: \"`cons` is like `insert` but pickier -- it demands
proof that you are not adding a duplicate. The extra demand carries useful
information for later reasoning.\"
"

/-- `Finset.cons a s h` adds element `a` to finset `s`, given a proof
`h : a ∉ s` that `a` is not already in `s`.

Unlike `insert`, `cons` requires this non-membership proof upfront. The
bridge lemma `Finset.cons_eq_insert` shows they produce the same result:
`Finset.cons a s h = insert a s`. -/
DefinitionDoc Finset.cons as "Finset.cons"

/-- `Finset.cons_eq_insert a s h` states that `Finset.cons a s h = insert a s`.
The finset built with `cons` (which requires a non-membership proof) equals the
one built with `insert` (which does not). -/
TheoremDoc Finset.cons_eq_insert as "Finset.cons_eq_insert" in "Finset"

NewDefinition Finset.cons
NewTheorem Finset.cons_eq_insert
DisabledTactic trivial decide native_decide simp aesop simp_all
