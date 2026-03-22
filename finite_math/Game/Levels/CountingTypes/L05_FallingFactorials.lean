import Game.Metadata

World "CountingTypes"
Level 5

Title "Falling Factorials"

Introduction "
# The Falling Factorial

How many ways can you pick 3 items from `n` in order (no repeats)?
For the first pick you have `n` choices, then `n - 1`, then `n - 2`:
$n \\times (n-1) \\times (n-2)$.

When `n = 5`, this is $5 \\times 4 \\times 3 = 60$.

This product has a name: the **falling factorial** (or **descending
factorial**), written `Nat.descFactorial n k`. It computes:

$$n^{\\underline{k}} = n \\cdot (n-1) \\cdot (n-2) \\cdots (n-k+1)$$

The recursive definition uses two lemmas:
- `Nat.descFactorial_zero n : n.descFactorial 0 = 1`
- `Nat.descFactorial_succ n k : n.descFactorial (k+1) = (n - k) * n.descFactorial k`

**Your task**: Given `n = 5`, prove that `n.descFactorial 3 = 60`.
First substitute the concrete value with `rw [hn]`, then unfold three
times with `descFactorial_succ` and close with `descFactorial_zero`.
"

/-- The falling factorial 5 * 4 * 3 = 60. -/
Statement (n : ℕ) (hn : n = 5) : n.descFactorial 3 = 60 := by
  Hint "The variable `n` blocks computation. Replace it with its
  concrete value first."
  Hint (hidden := true) "Try `rw [hn]`."
  rw [hn]
  Hint "The goal is `5.descFactorial 3 = 60`. The falling factorial
  unfolds one factor at a time using its recursive rule. Peel off the
  first factor."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "One factor down. Keep unfolding — peel off the next factor."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "Two factors down. One more unfolding exposes the base case."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "The base case `descFactorial 0` equals 1. Close it."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_zero]

Conclusion "
$$5^{\\underline{3}} = 5 \\times 4 \\times 3 = 60$$

The falling factorial counts **ordered selections without replacement**:
choosing `k` items from `n` where order matters and no item is repeated.

| Unfolding step | Result |
|---|---|
| `rw [hn]` | concrete: `5.descFactorial 3 = 60` |
| `descFactorial_succ` (k=2) | $(5 - 2) \\times 5^{\\underline{2}}$ |
| `descFactorial_succ` (k=1) | $3 \\times (5 - 1) \\times 5^{\\underline{1}}$ |
| `descFactorial_succ` (k=0) | $3 \\times 4 \\times (5 - 0) \\times 5^{\\underline{0}}$ |
| `descFactorial_zero` | $3 \\times 4 \\times 5 \\times 1 = 60$ |

**Note on factor order**: The factors appear as $3, 4, 5$ (ascending), not
$5, 4, 3$ (descending). This is because `descFactorial_succ` peels off
`(n - k)` starting from the largest `k`, so the recursion works bottom-up
even though the mathematical narrative goes top-down. The product is the
same either way.

Special cases:
- $n^{\\underline{0}} = 1$ (empty selection)
- $n^{\\underline{1}} = n$ (one choice)
- $n^{\\underline{n}} = n!$ (all items = permutation)

**Boundary case**: When $k > n$, the falling factorial is zero:
$n^{\\underline{k}} = 0$. You can't select more items than exist without
replacement. This is the counting-theoretic version of the pigeonhole
principle — if you have more pigeons than holes, no injection exists.
"

/-- `Nat.descFactorial n k` computes the falling factorial
$n \\cdot (n-1) \\cdots (n-k+1)$, the number of ways to choose `k`
items from `n` in order without replacement.

## Key lemmas
- `Nat.descFactorial_zero n : n.descFactorial 0 = 1`
- `Nat.descFactorial_succ n k : n.descFactorial (k+1) = (n - k) * n.descFactorial k`

## Special cases
- `Nat.descFactorial_one n : n.descFactorial 1 = n`
- `Nat.descFactorial_self n : n.descFactorial n = n !`
-/
DefinitionDoc Nat.descFactorial as "Nat.descFactorial"

/-- `Nat.descFactorial_succ n k` unfolds one step of the falling factorial:
`n.descFactorial (k + 1) = (n - k) * n.descFactorial k`.

## Syntax
```
rw [Nat.descFactorial_succ]
```

## When to use it
When you need to compute a falling factorial by peeling off one factor
at a time. Repeat until you reach `descFactorial 0`.
-/
TheoremDoc Nat.descFactorial_succ as "Nat.descFactorial_succ" in "Fintype"

/-- `Nat.descFactorial_zero n` is the base case: `n.descFactorial 0 = 1`.

## Syntax
```
rw [Nat.descFactorial_zero]
```

## When to use it
After unfolding `descFactorial_succ` enough times to reach `k = 0`.
-/
TheoremDoc Nat.descFactorial_zero as "Nat.descFactorial_zero" in "Fintype"

NewDefinition Nat.descFactorial
NewTheorem Nat.descFactorial_succ Nat.descFactorial_zero

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Force full recursive unfolding
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
