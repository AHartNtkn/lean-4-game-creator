import Game.Metadata

World "BinomialCoefficients"
Level 3

Title "Pascal's Identity"

Introduction "
# Pascal's Identity

The heart of the binomial coefficient is **Pascal's identity**:

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

This says: to choose $k+1$ items from $n+1$ items, either:
- **Include** a fixed element (then choose $k$ more from the remaining $n$), or
- **Exclude** it (then choose all $k+1$ from the remaining $n$)

In Lean, this is the defining equation of `Nat.choose`:
```
Nat.choose_succ_succ :
  Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)
```

**Your task**: Verify Pascal's identity for $n = 5, k = 2$:
$\\binom{6}{3} = \\binom{5}{2} + \\binom{5}{3}$.
"

/-- `Nat.choose_succ_succ` states that
`Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)`.

This is **Pascal's identity**: the recursive structure of binomial
coefficients.

## Syntax
```
rw [Nat.choose_succ_succ]
```

## When to use it
When you see `Nat.choose (n + 1) (k + 1)` (or equivalently a concrete
value like `Nat.choose 6 3`) and want to expand it recursively.

## Meaning
To choose $k+1$ items from $n+1$: either include a specific element
(choose $k$ from the rest) or exclude it (choose $k+1$ from the rest).

## Warning
`rw [Nat.choose_succ_succ]` rewrites **all** matching occurrences of
`Nat.choose (n + 1) (k + 1)` in the goal simultaneously. If multiple
terms match the pattern, they will all be expanded at once.
-/
TheoremDoc Nat.choose_succ_succ as "Nat.choose_succ_succ" in "Choose"

/-- Pascal's identity: C(6, 3) = C(5, 2) + C(5, 3). -/
Statement : Nat.choose 6 3 = Nat.choose 5 2 + Nat.choose 5 3 := by
  Hint "Use Pascal's identity to expand `Nat.choose 6 3`.
  Since $6 = 5 + 1$ and $3 = 2 + 1$, this matches the pattern."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]

Conclusion "
Pascal's identity is the engine of **Pascal's triangle**:
```
          1
         1 1
        1 2 1
       1 3 3 1
      1 4 6 4 1
     1 5 10 10 5 1
```

Each entry is the sum of the two entries above it.
The boundary values (`choose_zero_right` and `choose_self`)
give the $1$s along the edges; Pascal's identity fills in
the interior.

In the next level, you'll use Pascal's identity **repeatedly** to
compute a specific binomial coefficient from scratch.
"

NewTheorem Nat.choose_succ_succ

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
