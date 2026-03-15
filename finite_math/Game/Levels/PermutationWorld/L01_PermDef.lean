import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 1

Title "Equiv.Perm: a permutation is a bijection"

Introduction
"
# Permutations of Finite Types

Welcome to the world of **permutations**!

## The idea

A **permutation** of a set is a bijection from the set to itself — a
rearrangement of its elements. If you have a set $\\{0, 1, 2\\}$, a
permutation might send $0 \\mapsto 1$, $1 \\mapsto 2$, $2 \\mapsto 0$.

The set of all permutations of an $n$-element set forms a group called
the **symmetric group** $S_n$, with $n!$ elements.

## `Equiv.Perm` in Mathlib

In Lean, a permutation of a type `α` is an element of `Equiv.Perm α`,
which is defined as `α ≃ α` — the type of equivalences (bijections)
from `α` to itself.

Since `Equiv.Perm α` is just `α ≃ α`, a permutation `σ : Equiv.Perm α`
can be applied to any `x : α` to get `σ x : α`.

## Swaps

The simplest nontrivial permutation is a **swap** (or transposition):
it exchanges two elements and fixes everything else.

Mathlib provides `Equiv.swap a b : Equiv.Perm α`, which swaps `a` and `b`.
The key evaluation rules are:

```
Equiv.swap_apply_left  : (Equiv.swap a b) a = b
Equiv.swap_apply_right : (Equiv.swap a b) b = a
```

## Your task

Prove that swapping `0` and `1` in `Fin 3` sends `0` to `1`.
"

/-- Swapping `0` and `1` sends `0` to `1`. -/
Statement : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by
  Hint "Use `rw [Equiv.swap_apply_left]` to evaluate the swap at its
  left argument. The lemma `Equiv.swap_apply_left` says
  `(Equiv.swap a b) a = b`."
  Hint (hidden := true) "Try `rw [Equiv.swap_apply_left]`."
  rw [Equiv.swap_apply_left]

Conclusion
"
You evaluated a swap at one of the elements it exchanges.

## The three swap evaluation rules

When evaluating `(Equiv.swap a b) x`, there are three cases:

| Case | Lemma | Result |
|------|-------|--------|
| `x = a` | `Equiv.swap_apply_left` | `b` |
| `x = b` | `Equiv.swap_apply_right` | `a` |
| `x ≠ a` and `x ≠ b` | `Equiv.swap_apply_of_ne_of_ne` | `x` |

A swap only moves the two elements it exchanges; everything else is fixed.

**In plain language**: \"A transposition swaps two elements and leaves
everything else alone. `swap_apply_left` is the formal way to read off
where the first element goes.\"
"

/-- `Equiv.Perm α` is the type of permutations of `α`, defined as
`α ≃ α` — bijections from `α` to itself.

A permutation `σ : Equiv.Perm α` can be applied to any `x : α`
to get `σ x : α`.

**Key constructions**:
- `Equiv.swap a b` — the transposition swapping `a` and `b`
- `1 : Equiv.Perm α` — the identity permutation (fixes everything)

**Group structure**: `Equiv.Perm α` forms a group under composition. -/
DefinitionDoc Equiv.Perm as "Equiv.Perm"

/-- `Equiv.swap a b` is the transposition that swaps `a` and `b` and
fixes all other elements.

**Type**: `Equiv.swap (a b : α) [DecidableEq α] : Equiv.Perm α`

**Evaluation rules**:
- `Equiv.swap_apply_left : (Equiv.swap a b) a = b`
- `Equiv.swap_apply_right : (Equiv.swap a b) b = a`
- `Equiv.swap_apply_of_ne_of_ne : x ≠ a → x ≠ b → (Equiv.swap a b) x = x` -/
DefinitionDoc Equiv.swap as "Equiv.swap"

/-- `Equiv.swap_apply_left` evaluates a swap at its left argument:

`(Equiv.swap a b) a = b`

**When to use**: When the argument to a swap matches the first element
being swapped. -/
TheoremDoc Equiv.swap_apply_left as "Equiv.swap_apply_left" in "Equiv.Perm"

/-- `Equiv.swap_apply_right` evaluates a swap at its right argument:

`(Equiv.swap a b) b = a`

**When to use**: When the argument to a swap matches the second element
being swapped. -/
TheoremDoc Equiv.swap_apply_right as "Equiv.swap_apply_right" in "Equiv.Perm"

NewDefinition Equiv.Perm Equiv.swap
NewTheorem Equiv.swap_apply_left Equiv.swap_apply_right
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
