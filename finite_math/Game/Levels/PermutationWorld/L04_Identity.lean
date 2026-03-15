import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 4

Title "The identity permutation"

Introduction
"
# The Identity Permutation

Every group has an **identity element** — the element that does nothing.
For the symmetric group $S_n$, the identity permutation fixes every
element: $\\mathrm{id}(x) = x$ for all $x$.

## `1` and `Equiv.refl`

In Lean, the identity permutation is written as `1 : Equiv.Perm α`.
Under the hood, it equals `Equiv.refl α`:

```
Equiv.Perm.one_def : (1 : Equiv.Perm α) = Equiv.refl α
```

The reflexivity equivalence `Equiv.refl α` is the identity function on `α`:
it sends every element to itself. After rewriting with `one_def`, applying
the result to any `x` gives `x` by `rfl`.

## Self-inverse property

The identity also arises from composing a swap with itself. Since a
swap just exchanges two elements, doing it twice returns everything to
its original position:

```
Equiv.swap_mul_self : Equiv.swap a b * Equiv.swap a b = 1
```

## Your task

Prove that every element of `Fin 3` is fixed by the identity permutation.
"

/-- The identity permutation fixes every element of `Fin 3`. -/
Statement : ∀ x : Fin 3, (1 : Equiv.Perm (Fin 3)) x = x := by
  Hint "Start with `intro x` to introduce the universally quantified variable."
  intro x
  Hint "Now rewrite the identity permutation using `Equiv.Perm.one_def`.
  This replaces `1` with `Equiv.refl (Fin 3)`."
  rw [Equiv.Perm.one_def]
  Hint "The goal is now `(Equiv.refl (Fin 3)) x = x`. The reflexivity
  equivalence is the identity function, so this holds by `rfl`."
  Hint (hidden := true) "Try `rfl`."
  rfl

Conclusion
"
You proved that the identity permutation fixes every element.

## The identity in the group structure

The identity `1 : Equiv.Perm α` satisfies the group axioms:
- **Left identity**: `1 * σ = σ` for all `σ`
- **Right identity**: `σ * 1 = σ` for all `σ`

These are automatic consequences of the group structure on `Equiv.Perm α`.

## Connection to self-inverse

You will not need it in this world, but it is worth knowing:
`Equiv.swap_mul_self` says that `Equiv.swap a b * Equiv.swap a b = 1`.
Every transposition is its own inverse!

**In plain language**: \"The identity permutation is the 'do nothing'
bijection. In Lean, it is `1 : Equiv.Perm α`, which unfolds to
`Equiv.refl α` — the identity function.\"
"

/-- `Equiv.Perm.one_def` unfolds the identity permutation:

`(1 : Equiv.Perm α) = Equiv.refl α`

After rewriting, `(Equiv.refl α) x = x` holds by `rfl`.

**When to use**: When simplifying expressions involving the identity
permutation `1`. -/
TheoremDoc Equiv.Perm.one_def as "Equiv.Perm.one_def" in "Equiv.Perm"

/-- `Equiv.swap_mul_self` says that any swap is its own inverse:

`Equiv.swap a b * Equiv.swap a b = 1`

**When to use**: To show that composing a transposition with itself
gives the identity. -/
TheoremDoc Equiv.swap_mul_self as "Equiv.swap_mul_self" in "Equiv.Perm"

NewTheorem Equiv.Perm.one_def Equiv.swap_mul_self
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
