import Game.Metadata

World "Products"
Level 16

Title "Off-Diagonal Factored Form"

Introduction "
# The Permutation Formula

The off-diagonal cardinality formula from `offDiag_card` is:

$$|s.\\text{offDiag}| = |s|^2 - |s|$$

But in combinatorics textbooks, this quantity is usually written
in **factored form**:

$$|s.\\text{offDiag}| = |s| \\cdot (|s| - 1) = P(n, 2)$$

This is the number of **2-permutations** of an $n$-element set:
ordered selections of 2 distinct elements.

The factoring uses the identity $n^2 - n = n(n - 1)$, which in
Lean is `Nat.mul_sub_one`:

```
Nat.mul_sub_one : n * (m - 1) = n * m - n
```

**Your task**: Prove the general factored form for any finset `s`.
"

/-- The off-diagonal cardinality in factored form. -/
Statement (s : Finset ℕ) :
    s.offDiag.card = s.card * (s.card - 1) := by
  Hint "Start by expressing the off-diagonal cardinality using
  `Finset.offDiag_card`."
  Hint (hidden := true) "Try `rw [Finset.offDiag_card]`."
  rw [Finset.offDiag_card]
  Hint "Now you need to show `s.card * s.card - s.card = s.card * (s.card - 1)`.
  Use `Nat.mul_sub_one` — it says `n * (m - 1) = n * m - n`,
  which is exactly the reverse of this equation."
  Hint (hidden := true) "Try `rw [Nat.mul_sub_one]`.
  The `←` direction isn't needed here because `Nat.mul_sub_one`
  rewrites in the direction that matches the goal."
  rw [Nat.mul_sub_one]

Conclusion "
You've proved the **general** factored form:

$$|s.\\text{offDiag}| = |s| \\cdot (|s| - 1)$$

This holds for any finset `s` — no specific cardinality assumed.

**The combinatorial reading**: Choosing an ordered pair of distinct
elements from an $n$-element set means choosing the first element
($n$ choices) then the second ($n - 1$ remaining choices), giving
$n(n-1)$ total. This is the 2-permutation count $P(n, 2)$.

**Connection to binomial coefficients**: Since each unordered pair
corresponds to two ordered pairs (the symmetry from Level 13):

$$|s.\\text{offDiag}| = n(n-1) = 2 \\cdot \\binom{n}{2}$$

This bridges the *product-counting* framework (offDiag) with
the *subset-counting* framework (choose). The handshake lemma
is the classic instance: $n$ people shake hands
$\\binom{n}{2} = n(n-1)/2$ times.
"

/-- `Nat.mul_sub_one` factors natural number subtraction:

`n * (m - 1) = n * m - n`

## Syntax
```
rw [Nat.mul_sub_one]
```

## When to use it
When you need to factor `n * m - n` into `n * (m - 1)`, or
vice versa. Commonly used with `offDiag_card` to convert
between the squared form and the factored form.

## Warning
This is a natural number identity, so it holds even when
`m = 0` (both sides are 0). No side conditions needed.
-/
TheoremDoc Nat.mul_sub_one as "Nat.mul_sub_one" in "Arithmetic"

TheoremTab "Product"
NewTheorem Nat.mul_sub_one

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
