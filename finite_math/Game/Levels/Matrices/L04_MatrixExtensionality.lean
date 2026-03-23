import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 4

Title "Matrix Extensionality"

Introduction "
# When Are Two Matrices Equal?

Two matrices are equal when they agree at **every entry**. This is
`Matrix.ext_iff`:

$$M = N \\iff \\forall\\ i\\ j,\\; M\\,i\\,j = N\\,i\\,j$$

You already know this pattern from the Fin Tuples world: two functions
are equal when they agree on all inputs. Since matrices ARE functions
(of two arguments), matrix extensionality is just function
extensionality applied twice.

The tactic `ext i j` converts a goal `M = N` into a goal
`M i j = N i j` where `i` and `j` are fresh index variables. This
is the matrix version of the `ext` tactic you used for tuples.

**Your task**: Given that `M` and `N` agree at every entry, prove
they are equal.
"

/-- Two matrices that agree at every entry are equal. -/
Statement (M N : Matrix (Fin 2) (Fin 2) ℤ) (h : ∀ i j, M i j = N i j) : M = N := by
  Hint "The goal is `M = N`. Use `ext i j` to reduce this to showing
  they agree at each entry."
  Hint (hidden := true) "Try `ext i j`. This introduces index variables
  `i : Fin 2` and `j : Fin 2` and changes the goal to `M i j = N i j`."
  ext i j
  Hint "Now the goal is `M i j = N i j`. The hypothesis `h` tells you
  exactly this for all `i` and `j`."
  Hint (hidden := true) "Try `exact h i j`."
  exact h i j

Conclusion "
`ext i j` is the standard opening move when you need to prove two
matrices are equal. It reduces the problem to checking each entry.

This is the same `ext` you used for tuples (`Fin n → α`), but now
applied to functions of two arguments (`Fin m → Fin n → α`). The
tactic introduces BOTH index variables at once.

**Pattern**: To prove `M = N`, use `ext i j` then show `M i j = N i j`.

In plain mathematics, this is the obvious fact that two matrices
are equal iff they have the same entries. In Lean, you need to
invoke this fact explicitly because matrix equality is not checked
entry-by-entry by default — the kernel compares the matrices as
whole objects.
"

/-- `Matrix.ext_iff` characterizes matrix equality:

`M = N ↔ ∀ i j, M i j = N i j`

Two matrices are equal exactly when they agree at every entry.

## Syntax (tactic form)
```
ext i j    -- introduces i and j, changes goal from M = N to M i j = N i j
```

## Syntax (term form)
```
Matrix.ext (fun i j => ...)    -- build proof from entry-wise proof
```

## When to use it
When the goal is `M = N` for two matrices `M` and `N`.

## Example
After `ext i j`, the goal `Mᵀᵀ = M` becomes `Mᵀᵀ i j = M i j`.
-/
TheoremDoc Matrix.ext_iff as "Matrix.ext_iff" in "Matrix"

TheoremTab "Matrix"
NewTheorem Matrix.ext_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
