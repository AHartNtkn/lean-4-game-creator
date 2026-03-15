import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 7

Title "Nat is NOT a Fintype"

Introduction
"
# Not every type is finite

So far, every type you have encountered --- `Fin n`, `Bool`, products of
fintypes --- has had a `Fintype` instance. But not every type is finite.

## `Nat` has no `Fintype` instance

The natural numbers `Nat` form an infinite type. There is no finset that
contains *all* natural numbers. If you tried to write:

```
#check (Finset.univ : Finset Nat)
```

Lean would produce the error:

```
failed to synthesize instance
  Fintype Nat
```

This is analogous to the `DecidableEq` error you saw in an earlier world:
when a required type class instance does not exist, Lean refuses to proceed.

## Why this matters

The `Fintype` class is a *guarantee of finiteness*. When a lemma has
`[Fintype α]` in its signature, it means the lemma only applies to finite
types. This is not a limitation --- it is a feature. Cardinality only makes
sense for finite types, and Lean's type system ensures you never accidentally
try to count the elements of an infinite type.

## Your task

To illustrate that `Fintype` is a real constraint, prove a fact that
*uses* the `Fintype` class: show that every element of `Bool` belongs
to `Finset.univ`, and that `Finset.univ` for `Bool` has exactly 2 elements.

This combines `Finset.mem_univ` (from L02) with `Finset.card_univ` and
`Fintype.card_bool` (from L03 and L05). The point: these tools only
work because `Bool` *has* a `Fintype` instance. For `Nat`, they would fail.
"

/-- Every `Bool` is in `Finset.univ`, and `Finset.univ` for `Bool` has 2 elements. -/
Statement : (∀ b : Bool, b ∈ (Finset.univ : Finset Bool)) ∧
    (Finset.univ : Finset Bool).card = 2 := by
  Hint "This is a conjunction. Split it with `constructor`."
  constructor
  · Hint "For the first part, introduce `b` and use `Finset.mem_univ`.
    Try `intro b` then `exact Finset.mem_univ b`."
    Hint (hidden := true) "Use `intro b` followed by `exact Finset.mem_univ b`."
    intro b
    exact Finset.mem_univ b
  · Hint "For the second part, rewrite `Finset.univ.card` to `Fintype.card Bool`
    using `Finset.card_univ`, then use `Fintype.card_bool`.
    Try `rw [Finset.card_univ, Fintype.card_bool]`."
    Hint (hidden := true) "Use `rw [Finset.card_univ, Fintype.card_bool]`.
    Or simply `rfl` (since Lean can compute both sides)."
    rw [Finset.card_univ, Fintype.card_bool]

Conclusion
"
You proved two facts about `Bool` that depend on it having a `Fintype`
instance:
1. Every `Bool` belongs to `Finset.univ` (via `Finset.mem_univ`).
2. `Finset.univ` for `Bool` has 2 elements (via `Finset.card_univ` +
   `Fintype.card_bool`).

## The counterexample: `Nat`

Neither of these statements can even be *stated* for `Nat`, because
`Finset.univ : Finset Nat` does not exist. The `Fintype` instance is
a prerequisite, and `Nat` does not have one.

This is how Lean enforces finiteness: not by runtime checks, but by
requiring a `Fintype` instance at the type level. If the instance does
not exist, the code does not compile.

## Analogy to `DecidableEq`

Recall that `Finset` operations like `insert` require `DecidableEq`.
Similarly, `Finset.univ` and `Fintype.card` require `Fintype`. Both
are type classes that Lean synthesizes automatically when possible ---
and refuses when impossible.

**In plain language**: \"Not every type is finite. The natural numbers
are infinite, so there is no way to list all of them in a finset.
Lean enforces this by refusing to synthesize a `Fintype Nat` instance.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
