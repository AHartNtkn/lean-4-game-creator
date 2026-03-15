import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 4

Title "Injectivity by exhaustion"

Introduction
"
# Proving Injectivity by Exhaustion

A function `f : α → β` is **injective** if different inputs always
produce different outputs: whenever `f a = f b`, we must have `a = b`.

In Lean, `Function.Injective f` unfolds to `∀ a b, f a = f b → a = b`.

For functions on small finite types, we can prove injectivity by
checking every pair of inputs. If `f : Fin 3 → Fin 3`, there are
only `3 × 3 = 9` pairs to consider.

## The function

Consider the \"cyclic shift\" on `Fin 3`, defined as a lookup table:
```
f 0 = 1
f 1 = 2
f 2 = 0
```

This shifts every element forward by one (wrapping around). Since the
three outputs `1`, `2`, `0` are all distinct, the function is injective.

## Your task

Prove that this function is injective. After `intro a b h`, use
`fin_cases a <;> fin_cases b` to enumerate all 9 pairs. In each case,
`h` is a concrete equation between `Fin 3` elements.

For the 3 diagonal cases (where `a = b`), the goal `a = b` follows
by `rfl`. For the 6 off-diagonal cases (where `a ≠ b`), the hypothesis
`h` is a false equation (like `1 = 2`), so you can derive `False`.

The pattern for the contradictory cases:
`exfalso; have := congr_arg Fin.val h; norm_num at this`

This extracts the value-level equation from `h` and lets `norm_num`
find the arithmetic contradiction.
"

/-- The cyclic shift on `Fin 3` is injective. -/
Statement : Function.Injective
    (fun i : Fin 3 => match i with | 0 => (1 : Fin 3) | 1 => 2 | 2 => 0) := by
  Hint "Unfold `Function.Injective`: introduce two elements and the hypothesis
  that their images are equal. Try `intro a b h`."
  intro a b h
  Hint "Now enumerate all 9 pairs `(a, b)` from `Fin 3 × Fin 3`.
  Try `fin_cases a <;> fin_cases b`."
  Hint (hidden := true) "After `fin_cases a <;> fin_cases b`, you will have 9 goals.
  For cases where `a = b`, the goal is `rfl`. For cases where `a ≠ b`, `h` is a
  false equation. Use:
  `fin_cases a <;> fin_cases b <;>
    first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)`"
  fin_cases a <;> fin_cases b <;>
    first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)

/-- `Function.Injective f` means `∀ a b, f a = f b → a = b`. A function is
injective (or \"one-to-one\") if distinct inputs always produce distinct outputs.

**In Lean**: After `intro a b h`, you have `h : f a = f b` and must prove `a = b`.
On small finite types, use `fin_cases a <;> fin_cases b` to check all pairs.

**Example**: The identity function is injective. A constant function (on a type
with more than one element) is not. -/
DefinitionDoc Function.Injective as "Function.Injective"

NewDefinition Function.Injective
NewHiddenTactic first exfalso

DisabledTactic trivial decide native_decide simp aesop simp_all

Conclusion
"
The cyclic shift `0 ↦ 1, 1 ↦ 2, 2 ↦ 0` on `Fin 3` is injective. The proof
enumerated all 9 pairs:

| `a` | `b` | `f a` | `f b` | `f a = f b`? | `a = b`? |
|-----|-----|-------|-------|-------------|---------|
|  0  |  0  |   1   |   1   |  ✓ (trivial) | ✓ |
|  0  |  1  |   1   |   2   |  ✗ (vacuous) | -- |
|  0  |  2  |   1   |   0   |  ✗ (vacuous) | -- |
|  1  |  0  |   2   |   1   |  ✗ (vacuous) | -- |
|  1  |  1  |   2   |   2   |  ✓ (trivial) | ✓ |
|  1  |  2  |   2   |   0   |  ✗ (vacuous) | -- |
|  2  |  0  |   0   |   1   |  ✗ (vacuous) | -- |
|  2  |  1  |   0   |   2   |  ✗ (vacuous) | -- |
|  2  |  2  |   0   |   0   |  ✓ (trivial) | ✓ |

The 6 off-diagonal cases have `f a ≠ f b`, so the hypothesis
`h : f a = f b` is false --- the implication `f a = f b → a = b`
holds vacuously. The 3 diagonal cases have `a = b`, so the
conclusion holds by `rfl`.

**Proof move**: `intro a b h; fin_cases a <;> fin_cases b <;> closer`
is the brute-force injectivity proof for functions on small `Fin n`.
The closer handles both trivial equalities (`rfl`) and contradictions
(`exfalso` + `congr_arg Fin.val` + `norm_num`).

**The `Fin.val` extraction move**: The pattern
`have := congr_arg Fin.val h; norm_num at this` is a general technique
for deriving contradictions from false `Fin n` equations. It extracts
the underlying natural number equation from a `Fin n` equation and
lets `norm_num` find the arithmetic contradiction. You will see this
move repeatedly throughout this world.

**Same-domain matters**: Notice that the function maps `Fin 3` to
`Fin 3` (not `Fin 3` to `Fin 5`). When domain and codomain have the
same size, injectivity is especially interesting --- it means the
function is a permutation.

**In plain language**: \"The function $f$ with $f(0)=1$, $f(1)=2$, $f(2)=0$
is injective because its outputs $1, 2, 0$ are all distinct.\"
"
