import Game.Metadata

World "BinomialCoefficients"
Level 6

Title "Symmetry"

Introduction "
# Symmetry of Binomial Coefficients

Choosing $k$ items from $n$ is the same as choosing which $n - k$
items to **leave out**:

$$\\binom{n}{k} = \\binom{n}{n - k}$$

This means Pascal's triangle is **symmetric**: each row reads the
same forwards and backwards.

In Lean:
```
Nat.choose_symm : k ≤ n → Nat.choose n (n - k) = Nat.choose n k
```

The hypothesis `k ≤ n` is needed because `Nat.choose n k = 0` when
$k > n$ (which you'll see in Level 8), and $0 = 0$ is trivially
symmetric — the interesting symmetry is within the range $0 \\le k \\le n$.

**Your task**: Prove $\\binom{10}{8} = \\binom{10}{2}$ using symmetry.

This is a **computation shortcut**: instead of expanding C(10, 8)
through 8 levels of Pascal's triangle, symmetry converts it to
C(10, 2), which needs only 2 levels.
"

/-- `Nat.choose_symm` states that `Nat.choose n (n - k) = Nat.choose n k`
when `k ≤ n`.

## Syntax
```
have h : k ≤ n := by omega
exact Nat.choose_symm h
```

## When to use it
When you need to convert `Nat.choose n k` to `Nat.choose n (n - k)`
(or vice versa) to simplify a computation. Computing C(10, 2)
is much easier than C(10, 8)!

## Example
`Nat.choose_symm (show 2 ≤ 10 by omega) : Nat.choose 10 8 = Nat.choose 10 2`

## Common misuse
Forgetting to provide the proof that `k ≤ n`. The hypothesis
is required because choose gives 0 outside the valid range.
-/
TheoremDoc Nat.choose_symm as "Nat.choose_symm" in "Choose"

/-- Disabled: directly proves symmetry via addition decomposition. -/
TheoremDoc Nat.choose_symm_add as "Nat.choose_symm_add" in "Choose"

/-- Disabled: directly proves symmetry from an addition equation. -/
TheoremDoc Nat.choose_symm_of_eq_add as "Nat.choose_symm_of_eq_add" in "Choose"

/-- C(10, 8) = C(10, 2): symmetry of binomial coefficients. -/
Statement : Nat.choose 10 8 = Nat.choose 10 2 := by
  Hint "Choosing 8 from 10 is the same as leaving out 2.
  Use `Nat.choose_symm` with a proof that `2 ≤ 10`.

  Step 1: Create the inequality proof with `have`.
  Step 2: Apply symmetry with `exact`."
  Hint (hidden := true) "Try `have h : 2 ≤ 10 := by omega`."
  have h : 2 ≤ 10 := by omega
  Hint "Now you have `h : 2 ≤ 10` in context. Use it with symmetry:
  `exact Nat.choose_symm h`."
  Hint (hidden := true) "Try `exact Nat.choose_symm h`."
  exact Nat.choose_symm h

Conclusion "
$\\binom{10}{8} = \\binom{10}{2} = 45$.

Symmetry is a powerful **computation shortcut**: instead of expanding
$\\binom{10}{8}$ through 8 levels of Pascal's triangle, convert to
$\\binom{10}{2}$ and expand through just 2 levels.

In general, when $k > n/2$, use `choose_symm` to get
$k' = n - k < n/2$, which requires fewer Pascal expansions.

**Pattern**: Create the inequality proof with `have h : k ≤ n := by omega`,
then `exact Nat.choose_symm h`. You can also use the inline style:
`exact Nat.choose_symm (by omega)`.
"

NewTheorem Nat.choose_symm

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
