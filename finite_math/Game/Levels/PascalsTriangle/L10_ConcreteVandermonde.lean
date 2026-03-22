import Game.Metadata

World "PascalsTriangle"
Level 10

Title "Concrete Vandermonde"

Introduction "
# The Vandermonde Identity: A Concrete Case

The most important convolution identity in combinatorics is the
**Vandermonde identity**:
$$\\binom{m + n}{k} = \\sum_{(i,j) \\in \\text{antidiagonal}(k)} \\binom{m}{i} \\cdot \\binom{n}{j}$$

In Lean, this is `Nat.add_choose_eq m n k`.

**Counting interpretation**: Imagine choosing $k$ people from a
group of $m$ men and $n$ women. You can split the $k$ chosen people
into $i$ men and $j = k - i$ women, where $i + j = k$. The number
of ways to choose $i$ men from $m$ is $\\binom{m}{i}$, and $j$ women
from $n$ is $\\binom{n}{j}$. Summing over all splits gives
$\\binom{m+n}{k}$. This is the most famous **double-counting**
argument in combinatorics.

Before proving it in full generality, verify it on a small case:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(2)} \\binom{3}{i} \\cdot \\binom{4}{j} = \\binom{7}{2}$$

The antidiagonal of 2 has three pairs: $(0,2), (1,1), (2,0)$.
The sum is:
$$\\binom{3}{0} \\cdot \\binom{4}{2} + \\binom{3}{1} \\cdot \\binom{4}{1} + \\binom{3}{2} \\cdot \\binom{4}{0} = 1 \\cdot 6 + 3 \\cdot 4 + 3 \\cdot 1 = 21 = \\binom{7}{2}$$

**Your task**: Prove this using `Nat.add_choose_eq` directly.
"

/-- `Nat.add_choose_eq` (the Vandermonde identity) states that
`(m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2`.

## Syntax
```
rw [Nat.add_choose_eq]
rw [← Nat.add_choose_eq]
exact Nat.add_choose_eq m n k
```

## When to use it
When you have a sum over the antidiagonal of products of binomial
coefficients and want to collapse it to a single binomial coefficient,
or vice versa. The identity decomposes `choose (m + n) k` into a
convolution over `antidiagonal k`.

## Key specializations
- `m = n = k = n`: gives `∑ choose n i * choose n j = choose (2n) n`
  (sum of squared binomial coefficients)
- `m = n, k = 0`: gives `choose (2n) 0 = 1` (trivial base case)
-/
TheoremDoc Nat.add_choose_eq as "Nat.add_choose_eq" in "Choose"

/-- Concrete Vandermonde: ∑ (i,j) with i+j=2 of C(3,i)*C(4,j) = C(7,2). -/
Statement :
    ∑ p ∈ Finset.antidiagonal 2,
      Nat.choose 3 p.1 * Nat.choose 4 p.2 = Nat.choose 7 2 := by
  Hint "The Vandermonde identity `Nat.add_choose_eq m n k` says:
  `(m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2`.

  With $m = 3$, $n = 4$, $k = 2$, the RHS matches your LHS.
  The LHS gives `(3 + 4).choose 2 = choose 7 2`.

  First rewrite `7` as `3 + 4` so the types match."
  Hint (hidden := true) "Try `have h : (7 : ℕ) = 3 + 4 := by omega`."
  have h : (7 : ℕ) = 3 + 4 := by omega
  Hint "Now rewrite the goal to use `3 + 4` instead of `7`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]
  Hint "The goal is now:
  `∑ p ∈ antidiagonal 2, choose 3 p.1 * choose 4 p.2 = (3 + 4).choose 2`.

  Flip the equation with `symm` so the Vandermonde identity
  matches directly."
  Hint (hidden := true) "Try `symm`."
  symm
  Hint "Now apply the Vandermonde identity."
  Hint (hidden := true) "Try `exact Nat.add_choose_eq 3 4 2`."
  exact Nat.add_choose_eq 3 4 2

Conclusion "
You verified:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(2)} \\binom{3}{i} \\cdot \\binom{4}{j} = \\binom{7}{2} = 21$$

**The reshape-flip-apply pattern**: This proof uses a
three-step strategy:
1. **Reshape** — rewrite the goal to match the lemma's form (`7 = 3 + 4`)
2. **Flip** — `symm` to orient the equation correctly
3. **Apply** — `exact` the lemma

This is a general-purpose **matching** strategy: when a known lemma
almost matches the goal but the form is slightly off, reshape the
goal first, then flip and apply. You used it in Level 2 with
`choose_symm`, and here with `add_choose_eq`.

**What Vandermonde says**: To compute $\\binom{m + n}{k}$, you can
split the $k$ chosen items into $i$ from the first group (of $m$)
and $j$ from the second group (of $n$), where $i + j = k$. Summing
over all ways to split gives the total.

**The general form**: The Vandermonde identity works for any
$m$, $n$, $k$: $\\sum_{(i,j) \\in \\text{antidiagonal}(k)}
\\binom{m}{i} \\cdot \\binom{n}{j} = \\binom{m+n}{k}$. The concrete
case is the same pattern — just `symm` then `exact Nat.add_choose_eq m n k`
(no reshape needed when $m + n$ already appears in the goal).
In the next level, you will specialize Vandermonde to
$m = n = k = n$ to get the **convolution** sum.
"

NewTheorem Nat.add_choose_eq

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
