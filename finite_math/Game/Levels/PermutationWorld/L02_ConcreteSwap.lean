import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 2

Title "Constructing a permutation of Fin 3"

Introduction
"
# A Concrete Permutation

In the previous level you saw that `Equiv.swap 0 1` sends `0` to `1`.
Now you will verify all three outputs of the swap `(0 1)` on `Fin 3`,
proving it is a complete description of a permutation.

## The three cases

For `Equiv.swap (0 : Fin 3) 1`:

| Input | Output | Why |
|-------|--------|-----|
| `0` | `1` | `swap_apply_left` |
| `1` | `0` | `swap_apply_right` |
| `2` | `2` | `swap_apply_of_ne_of_ne` (since `2 ≠ 0` and `2 ≠ 1`) |

## The third rule

When the argument is *neither* of the swapped elements, use:

```
Equiv.swap_apply_of_ne_of_ne : x ≠ a → x ≠ b → (Equiv.swap a b) x = x
```

You need to supply two proofs of inequality. For concrete `Fin n` values,
`by omega` can close these.

## Your task

Prove all three evaluation facts as a conjunction.
"

/-- The swap `(0 1)` on `Fin 3` sends `0 ↦ 1`, `1 ↦ 0`, and fixes `2`. -/
Statement : (Equiv.swap (0 : Fin 3) 1) 0 = 1 ∧
    (Equiv.swap (0 : Fin 3) 1) 1 = 0 ∧
    (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by
  Hint "Start with `refine ⟨?_, ?_, ?_⟩` to split into three goals.
  (Or use `constructor` twice.)"
  refine ⟨?_, ?_, ?_⟩
  · Hint "The first goal asks where `0` goes. Use `rw [Equiv.swap_apply_left]`."
    Hint (hidden := true) "Try `rw [Equiv.swap_apply_left]`."
    rw [Equiv.swap_apply_left]
  · Hint "The second goal asks where `1` goes. Use `rw [Equiv.swap_apply_right]`."
    Hint (hidden := true) "Try `rw [Equiv.swap_apply_right]`."
    rw [Equiv.swap_apply_right]
  · Hint "The third goal asks where `2` goes. Since `2 ≠ 0` and `2 ≠ 1`,
    use `rw [Equiv.swap_apply_of_ne_of_ne]` and supply the two inequality
    proofs.

    The full invocation is:
    `rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]`

    Here `by omega` proves each `Fin 3` inequality automatically."
    Hint (hidden := true) "Try `rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]`."
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

Conclusion
"
You verified the complete behavior of the swap `(0 1)` on `Fin 3`.

## Swaps as permutations

A swap `Equiv.swap a b` is fully determined by two elements. On a type
with $n$ elements, it fixes all $n - 2$ other elements. The three
evaluation lemmas (`swap_apply_left`, `swap_apply_right`,
`swap_apply_of_ne_of_ne`) let you compute the output for any input.

## A fact from algebra

Every permutation can be written as a product of transpositions. So
`Equiv.swap` is not just a simple example — it is a *generator* for the
entire symmetric group $S_n$.

**In plain language**: \"To describe a swap completely, you just need to
say which two elements it exchanges. Everything else stays put.\"
"

/-- `Equiv.swap_apply_of_ne_of_ne` evaluates a swap at an element that
is neither of the swapped elements:

`x ≠ a → x ≠ b → (Equiv.swap a b) x = x`

**When to use**: When the argument to a swap is different from both
elements being swapped. Supply two inequality proofs (e.g., `by omega`
for concrete `Fin n` values). -/
TheoremDoc Equiv.swap_apply_of_ne_of_ne as "Equiv.swap_apply_of_ne_of_ne" in "Equiv.Perm"

NewTheorem Equiv.swap_apply_of_ne_of_ne
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
