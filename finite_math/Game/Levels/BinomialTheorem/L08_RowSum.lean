import Game.Metadata

World "BinomialTheorem"
Level 8

Title "The Row Sum Identity"

Introduction "
# Row Sum: $\\sum \\binom{n}{m} = 2^n$

The sum of all entries in row $n$ of Pascal's triangle is $2^n$:

$$\\sum_{m=0}^{n} \\binom{n}{m} = 2^n$$

This is the most famous consequence of the binomial theorem.
Before proving the general case, notice the $n = 3$ instance:

$$\\binom{3}{0} + \\binom{3}{1} + \\binom{3}{2} + \\binom{3}{3}
= 1 + 3 + 3 + 1 = 8 = 2^3$$

The general proof: specialize `add_pow_nat` to `x = 1, y = 1`:

$$(1 + 1)^n = \\sum_{m=0}^{n} 1^m \\cdot 1^{n-m} \\cdot \\binom{n}{m}$$

The left side is $2^n$. The right side simplifies to
$\\sum \\binom{n}{m}$ after removing the powers of $1$.

**The specialize-simplify-rewrite pattern**: You are about to use
a 4-step proof method that recurs throughout this world:

1. **Specialize**: `have h := add_pow_nat x y n` — instantiate the
   binomial theorem with concrete values
2. **Simplify summands**: `have simpl : ∀ m ∈ ..., old = new := by ...`
   — prove each term simplifies (using `one_pow`, `one_mul`, etc.)
3. **Rewrite the hypothesis**: `rw [Finset.sum_congr rfl simpl] at h`
   — apply the simplification to the sum in `h`
4. **Close**: `exact h.symm` — flip and match the goal

Each step uses a tool you learned in Levels 4-7. Here you assemble
them for the first time into a complete derivation.
"

/-- The row sum of Pascal's triangle equals 2^n. -/
Statement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n := by
  Hint "Start by specializing the binomial theorem to x = 1, y = 1.
  Use `have h := add_pow_nat 1 1 n` to get the expansion of
  `(1 + 1) ^ n`."
  Hint (hidden := true) "Try `have h := add_pow_nat 1 1 n`."
  have h := add_pow_nat 1 1 n
  Hint "Now `h` says `(1 + 1) ^ n = ∑ m, 1^m * 1^(n-m) * choose n m`.

  The summand needs simplifying. Use the `have` + `sum_congr` pattern
  from Level 5: create a proof that each term simplifies, then rewrite.

  Declare the simplification:
  `have simpl : ∀ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by`"
  Hint (hidden := true) "Type:
  `have simpl : ∀ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by`

  Then in the sub-proof: `intro m _` followed by
  `rw [one_pow, one_pow, one_mul, one_mul]`."
  have simpl : ∀ m ∈ Finset.range (n + 1),
      1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by
    intro m _
    rw [one_pow, one_pow, one_mul, one_mul]
  Hint "Good — you have `simpl` proving the pointwise simplification.
  Now apply it to the sum in `h` using `rw [Finset.sum_congr rfl simpl] at h`.

  This rewrites the complicated sum in `h` to the simple sum
  `∑ m, choose n m`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl] at h`."
  rw [Finset.sum_congr rfl simpl] at h
  Hint "Now `h` says `(1 + 1) ^ n = ∑ m, choose n m`.

  The goal is `∑ m, choose n m = 2 ^ n`. The equation in `h` has
  the sides swapped relative to the goal (and `1 + 1 = 2`).
  Use `h.symm` to flip `h` from `a = b` to `b = a`, then
  `exact h.symm` closes the goal."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion "
You just derived the **row sum identity**:

$$\\sum_{m=0}^{n} \\binom{n}{m} = 2^n$$

This is `Nat.sum_range_choose` in Mathlib. From now on, you can
use it directly without re-deriving it.

You just completed the **specialize-simplify-rewrite pattern**
described in the introduction. The same 4-step skeleton —
specialize, simplify summands, rewrite the hypothesis, flip and
close — will produce different theorems with different input values.
You will use it again with `x = 2, y = 1` to derive a different
identity.

**Tools retrieved**:
- `have simpl` + `rw [Finset.sum_congr rfl simpl] at h` — simplify a sum in a hypothesis (Level 7)
- `h.symm` — flip `h : a = b` to `b = a` (Level 6)

**Why $2^n$?** Setting $x = y = 1$ collapses the variable powers:
$1^m = 1$ and $1^{n-m} = 1$. The only thing left in each summand
is the coefficient $\\binom{n}{m}$ itself. The left side $(1+1)^n = 2^n$
gives the total.

**Counting interpretation**: A set with $n$ elements has $2^n$
subsets in total. Summing the number of subsets of each size gives
$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$. You will make this connection
formal in the next level.
"

/-- `Nat.sum_range_choose` states that
`∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n`.

The sum of all binomial coefficients in row $n$ of Pascal's
triangle is $2^n$.

## Syntax
```
exact Nat.sum_range_choose n
rw [Nat.sum_range_choose]
```

## When to use it
When the goal has `∑ m ∈ Finset.range (n + 1), Nat.choose n m`
and you want to replace it with `2 ^ n`, or vice versa.

## Origin
Derived from `add_pow` by setting $x = y = 1$ and simplifying.
-/
TheoremDoc Nat.sum_range_choose as "Nat.sum_range_choose" in "Choose"

NewTheorem Nat.sum_range_choose

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
DisabledTheorem Nat.sum_range_choose
