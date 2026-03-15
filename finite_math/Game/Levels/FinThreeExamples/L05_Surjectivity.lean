import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 5

Title "Surjectivity by exhaustion"

Introduction
"
# Proving Surjectivity by Finding Preimages

A function `f : α → β` is **surjective** if every element of the
codomain is hit: for every `b : β`, there exists `a : α` with `f a = b`.

In Lean, `Function.Surjective f` unfolds to `∀ b, ∃ a, f a = b`.

## The function

Consider the same cyclic shift from the previous level:
```
f 0 = 1
f 1 = 2
f 2 = 0
```

Is this function surjective onto `Fin 3`? Yes! Every element of `Fin 3`
is hit:
- `0` is hit by `f 2 = 0`
- `1` is hit by `f 0 = 1`
- `2` is hit by `f 1 = 2`

## Your task

Prove that the cyclic shift is surjective. After `intro b`, use
`fin_cases b` to split into three cases --- one for each element of the
codomain. In each case, provide the preimage using `exact ⟨witness, rfl⟩`.

The `rfl` closes the equality because the function is defined by
pattern matching, so `f witness` computes to the target value.
"

/-- The cyclic shift on `Fin 3` is surjective. -/
Statement : Function.Surjective
    (fun i : Fin 3 => match i with | 0 => (1 : Fin 3) | 1 => 2 | 2 => 0) := by
  Hint "Unfold `Function.Surjective`: introduce a target element from the
  codomain. Try `intro b`."
  intro b
  Hint "Now split into cases for each element of `Fin 3` that `b` could be.
  Try `fin_cases b`."
  fin_cases b
  · Hint "The goal is `∃ a, f a = 0`. Which element maps to `0`?
    The cyclic shift sends `2 ↦ 0`. Try `exact ⟨2, rfl⟩`."
    exact ⟨2, rfl⟩
  · Hint "The goal is `∃ a, f a = 1`. Which element maps to `1`?
    The cyclic shift sends `0 ↦ 1`. Try `exact ⟨0, rfl⟩`."
    exact ⟨0, rfl⟩
  · Hint "The goal is `∃ a, f a = 2`. Which element maps to `2`?
    The cyclic shift sends `1 ↦ 2`. Try `exact ⟨1, rfl⟩`."
    exact ⟨1, rfl⟩

/-- `Function.Surjective f` means `∀ b, ∃ a, f a = b`. A function is surjective
(or \"onto\") if every element of the codomain is in the image of `f`.

**In Lean**: After `intro b`, you must find a preimage `a` with `f a = b`.
On small finite types, use `fin_cases b` to check each codomain element,
then provide the preimage with `exact ⟨witness, rfl⟩`.

**Example**: The identity function is surjective. A function from `Fin 3`
to `Fin 4` cannot be surjective (not enough inputs to cover all outputs). -/
DefinitionDoc Function.Surjective as "Function.Surjective"

NewDefinition Function.Surjective

DisabledTactic trivial decide native_decide simp aesop simp_all norm_num

Conclusion
"
The cyclic shift is surjective: every element of `Fin 3` has a preimage.

| Target `b` | Preimage `a` | Check: `f a = b` |
|-----------|-------------|-------------------|
|     0     |      2      | `f 2 = 0` ✓ |
|     1     |      0      | `f 0 = 1` ✓ |
|     2     |      1      | `f 1 = 2` ✓ |

**Proof shape**: `intro b; fin_cases b` → per-case `exact ⟨witness, rfl⟩`.
This is the dual of the injectivity proof: instead of checking all
*pairs* of inputs, you check all *outputs* and provide a preimage
for each one.

**Combining with injectivity**: You proved in the previous level
that the cyclic shift is injective, and now that it is surjective.
A function that is both injective and surjective is **bijective** ---
it is a one-to-one correspondence. On `Fin 3`, this means the cyclic
shift is a permutation.

**In plain language**: \"The function $f$ with $f(0)=1$, $f(1)=2$, $f(2)=0$
is surjective because every element of $\\{0, 1, 2\\}$ has a preimage:
$0 = f(2)$, $1 = f(0)$, $2 = f(1)$.\"
"
