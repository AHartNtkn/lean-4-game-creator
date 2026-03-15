import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 7

Title "Finset vs Set"

Introduction
"
# Two kinds of \"set\" in Lean

You may have encountered `Set α` in Lean before -- it represents an
arbitrary (possibly infinite) subset of `α`. Now you are working with
`Finset α`. They look similar but are **fundamentally different types**.

## The key differences

- **Size**: A `Set` can be infinite. A `Finset` is always finite.
- **Data**: A `Set α` is a predicate `α → Prop`. A `Finset` carries an
  explicit list of elements (with no duplicates).
- **Membership**: In a `Set`, membership is propositional. In a `Finset`,
  membership is decidable (computable).

## A common source of confusion

Because both use the `∈` notation and `{a, b, c}` syntax, it is easy
to confuse them. But their lemma libraries are **separate**:

- `Set.mem_union` works on `Set.union`
- `Finset.mem_union` works on `Finset.union`

If you tried to apply `Set.mem_union` to a `Finset` goal, you would get
a type error:

```
type mismatch
  Set.mem_union ...
has type
  ... ∈ s ∪ t ↔ ... ∈ s ∨ ... ∈ t : Prop
but is expected to have type
  ... ∈ (Finset ...) ...
```

The `Set.mem_union` lemma expects `Set.union`, but `Finset` union is a
different operation on a different type. You must use `Finset.mem_union`
instead. Always look for lemmas in the `Finset` namespace, not `Set`.

## Your task

Prove that `{1, 2, 3}` is nonempty as a finset. The definition
`Finset.Nonempty s` means `∃ a, a ∈ s`. You can prove it by providing
a witness with `use` and then proving membership.

The membership goal `1 ∈ ({1, 2, 3} : Finset Nat)` is a concrete
decidable proposition.
"

/-- The finset `{1, 2, 3}` is nonempty. -/
Statement : ({1, 2, 3} : Finset Nat).Nonempty := by
  Hint "The goal is `Finset.Nonempty ...`, which unfolds to
  an existential: there exists an element in the finset.
  To prove an existential, provide a witness with `use`."
  Hint (hidden := true) "Use `use 1` to provide the witness `1`. The
  remaining goal will be a concrete membership check."
  use 1
  Hint "The remaining goal is a concrete membership check: does the
  witness belong to the finset? This is decidable."
  Hint (hidden := true) "Try `decide`. Lean evaluates the membership
  check on concrete data.

  Note: if this were a `Set` instead of a `Finset`, you would need
  `Set.Nonempty` and `Set` lemmas. The types are incompatible."
  decide

Conclusion
"
You proved `Finset.Nonempty` by providing a witness (`1`) and verifying
membership. The two-step pattern -- `use` then verify -- is the standard
approach for existential goals.

## Why `Set` lemmas do not apply

If you had a `Set` instead of a `Finset`, you would use `Set.Nonempty`
and its own API. The proof structure might look similar, but the types
are incompatible -- you cannot apply `Set` lemmas to a `Finset`.

For example, `Set.mem_union` has type:
```
a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t   -- where s t : Set α
```
If you tried to use it on a `Finset`, you would get a type mismatch.
The correct `Finset` version is `Finset.mem_union`:
```
a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t   -- where s t : Finset α
```
Same statement, different type, different namespace.

## The takeaway

When searching for lemmas about finsets, **always look in the `Finset`
namespace**, not the `Set` namespace. The notation is the same, but the
types and lemma libraries are completely separate.

## When will we connect them?

Later in the course (World 20: Three Notions of Finiteness), you will
learn about the coercion from `Finset` to `Set` and the relationship
between `Set.Finite`, `Fintype`, and `Finset`. For now, treat them as
separate worlds with separate tools.

**In plain language**: \"A `Finset` is computationally finite -- its
elements are listed explicitly. A `Set` is a predicate -- it says
which elements are 'in' without necessarily listing them. The notation
looks the same, but the mathematical objects are different.\"
"

/-- `Finset.Nonempty s` means `∃ a, a ∈ s` -- the finset has at least one
element. Prove it by providing a witness with `use` and verifying membership.

Do not confuse with `Set.Nonempty`, which is for `Set α` not `Finset α`. -/
DefinitionDoc Finset.Nonempty as "Finset.Nonempty"

NewDefinition Finset.Nonempty
DisabledTactic trivial native_decide simp aesop simp_all
