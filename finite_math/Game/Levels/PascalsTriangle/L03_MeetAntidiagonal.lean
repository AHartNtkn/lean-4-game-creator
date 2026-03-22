import Game.Metadata

World "PascalsTriangle"
Level 3

Title "Meet the Antidiagonal"

Introduction "
# The Antidiagonal: Pairs That Sum to $n$

Look at row $n$ of Pascal's triangle. Each entry $\\binom{n}{k}$ is
indexed by **one** number $k$. But there is a natural way to index
by **two** numbers: the pair $(k, n - k)$.

The $n$-th **antidiagonal** is the set of all pairs $(i, j)$ of
natural numbers with $i + j = n$:

$$\\text{antidiagonal}(5) = \\{(0,5),\\; (1,4),\\; (2,3),\\; (3,2),\\; (4,1),\\; (5,0)\\}$$

In Lean, this is `Finset.antidiagonal n`. The key characterization:

```
Finset.mem_antidiagonal :
  p ∈ Finset.antidiagonal n ↔ p.1 + p.2 = n
```

A pair $(i, j)$ is in the $n$-th antidiagonal if and only if
$i + j = n$.

**Your task**: Prove that $(2, 3) \\in \\text{antidiagonal}(5)$.
"

/-- `Finset.antidiagonal n` is the finset of pairs `(i, j)` with
`i + j = n`.

## Syntax
```
Finset.antidiagonal n
```

## When to use it
When you want to sum over all pairs `(i, j)` with `i + j = n`,
or when you want to index into row `n` of Pascal's triangle
using both coordinates.

## Example
`Finset.antidiagonal 3 = {(0,3), (1,2), (2,1), (3,0)}`

## Warning
`antidiagonal n` contains `n + 1` elements (not `n`), because
the pairs range from `(0, n)` to `(n, 0)`.
-/
DefinitionDoc Finset.HasAntidiagonal.antidiagonal as "Finset.antidiagonal"

/-- `Finset.mem_antidiagonal` states that
`p ∈ Finset.antidiagonal n ↔ p.1 + p.2 = n`.

## Syntax
```
rw [Finset.mem_antidiagonal]
rw [Finset.mem_antidiagonal] at h
```

## When to use it
When you see `p ∈ Finset.antidiagonal n` and want to convert it
to the arithmetic condition `p.1 + p.2 = n`, or vice versa.

## Example
```
have h : (2, 3) ∈ Finset.antidiagonal 5 := by
  rw [Finset.mem_antidiagonal]
```
-/
TheoremDoc Finset.HasAntidiagonal.mem_antidiagonal as "Finset.mem_antidiagonal" in "Finset"

/-- (2, 3) is in the 5th antidiagonal. -/
Statement : (2, 3) ∈ Finset.antidiagonal 5 := by
  Hint "Use `Finset.mem_antidiagonal` to convert the membership
  question into an arithmetic equation: is $2 + 3 = 5$?"
  Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal]`."
  rw [Finset.mem_antidiagonal]
  Hint "The goal is now an arithmetic identity. Close it with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
$(2, 3) \\in \\text{antidiagonal}(5)$ because $2 + 3 = 5$. That is all
the antidiagonal means: pairs whose coordinates sum to $n$.

**Why antidiagonals?** The name comes from matrices. If you arrange
the pairs $(i, j)$ in a grid, the pairs with $i + j = n$ lie along
a diagonal running from top-right to bottom-left — the **anti**diagonal:

```
    j=0  j=1  j=2  j=3  j=4  j=5
i=0  [*]
i=1       [*]
i=2            [*]            <-- (2, 3) is here
i=3                 [*]
i=4                      [*]
i=5                           [*]
```

The starred entries are `antidiagonal 5`. In the next level, you will
see what is NOT in an antidiagonal.
"

NewDefinition Finset.HasAntidiagonal.antidiagonal
NewTheorem Finset.HasAntidiagonal.mem_antidiagonal

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
