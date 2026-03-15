import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 3

Title "Accessing entries and ext"

Introduction
"
# Accessing Entries and Matrix Extensionality

In the previous levels, you saw that `M i j` is just function application.
Now you will use this idea in reverse: to prove two matrices are equal,
it suffices to prove they agree at every entry.

## `ext` for matrices

The tactic `ext i j` reduces a goal `M = N` (where `M, N : Matrix m n α`)
to proving `M i j = N i j` for all `i` and `j`. This is **extensionality**
for functions — the same `ext` you used for `Fin` and `Finset` equality.

## `fin_cases`

After `ext i j` with `i j : Fin 2`, you get universally quantified
goals. Use `fin_cases i <;> fin_cases j` to split into the four
concrete cases `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`. Each case then
reduces by computation.

## The `!![...]` notation

The notation `!![1, 2; 3, 4]` builds a `Matrix (Fin 2) (Fin 2) Nat`
whose entries at concrete indices evaluate automatically.

## Your task

Prove that a matrix defined by a formula agrees with one defined by
literal notation.
"

/-- A function-defined matrix equals its literal representation. -/
Statement : (fun i j : Fin 2 => 2 * i.val + j.val + 1 : Matrix (Fin 2) (Fin 2) Nat) =
    !![1, 2; 3, 4] := by
  Hint "Use `ext i j` to reduce this to entry-wise equality.
  Then `fin_cases i <;> fin_cases j` splits into four concrete cases."
  ext i j
  Hint "Now you need to show the entries agree for specific `i` and `j`.
  Use `fin_cases i <;> fin_cases j` to enumerate all four index pairs."
  Hint (hidden := true) "Try `fin_cases i <;> fin_cases j <;> rfl`."
  fin_cases i <;> fin_cases j <;> rfl

Conclusion
"
You proved matrix equality by checking every entry — the `ext` tactic
applied extensionality, and `fin_cases` enumerated all index pairs.

## The pattern

To prove `M = N` for matrices over `Fin n`:

1. `ext i j` — reduce to entry-wise equality
2. `fin_cases i <;> fin_cases j` — enumerate all index pairs
3. Close each case by computation (`rfl`, `norm_num`, etc.)

This pattern works because `Fin n` is finite and Lean can enumerate
its elements.

## Why `<;>` ?

The semicolon combinator `<;>` applies the next tactic to **all** goals
produced by the previous tactic. So `fin_cases i <;> fin_cases j <;> rfl`
means: \"split on `i`, then split on `j` in each case, then close every
resulting goal with `rfl`.\"

**In plain language**: \"Two matrices are equal exactly when they agree
at every entry. For finite matrices, this is checkable by enumeration.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
