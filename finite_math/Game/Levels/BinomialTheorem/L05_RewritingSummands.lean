import Game.Metadata

World "BinomialTheorem"
Level 5

Title "Rewriting Inside Sums"

Introduction "
# Simplifying Summands with `sum_congr`

You know `one_pow` and `one_mul` can simplify `1^m * 1^k * c` to `c`.
But in the binomial theorem, these expressions appear **inside a sum**.
You need a way to apply the simplification to every term at once.

You learned `Finset.sum_congr` in BigOpAlgebra:
```
Finset.sum_congr (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x) :
  ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
```

The strategy: prove that each summand simplifies (the `∀ x ∈ s₂, ...`
part), then use `sum_congr rfl` to rewrite the entire sum.

**Your task**: Prove that the sum with `1^m * 1^(n-m) * choose n m`
equals the sum with just `choose n m`. You will use `apply` to reduce
the goal to a pointwise equality, then simplify each term.
"

/-- Simplifying summands involving powers of 1. -/
Statement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m =
    ∑ m ∈ Finset.range (n + 1), Nat.choose n m := by
  Hint "The two sums range over the same finset. Use
  `apply Finset.sum_congr rfl` to reduce the goal to showing
  that each summand is equal. This creates a goal:
  `∀ m ∈ Finset.range (n + 1), 1^m * 1^(n-m) * choose n m = choose n m`."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
  apply Finset.sum_congr rfl
  Hint "Good — the goal is now a universal statement. Introduce the
  bound variable `m` and the membership proof (which you don't need)."
  Hint (hidden := true) "Try `intro m _`."
  intro m _
  Hint "Now the goal is `1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m`.
  This is exactly the Level 4 pattern: use `one_pow` twice and
  `one_mul` twice."
  Hint (hidden := true) "Try `rw [one_pow, one_pow, one_mul, one_mul]`."
  rw [one_pow, one_pow, one_mul, one_mul]

Conclusion "
The pattern you just learned is the **sum simplification pattern**:

1. `apply Finset.sum_congr rfl` — reduce to pointwise equality
2. `intro m _` — introduce the bound variable
3. Rewrite chain — simplify each summand

This is a retrieval of `sum_congr` from BigOpAlgebra, applied in
the new context of binomial specialization. You will use this
exact pattern in Level 8 to derive the **row sum identity**.

**Alternative approach**: Instead of `apply`, you can use `have`
to name the pointwise proof and then `rw` with it:
```
have simpl : ∀ m ∈ Finset.range (n + 1), ... := by
  intro m _; rw [one_pow, one_pow, one_mul, one_mul]
rw [Finset.sum_congr rfl simpl]
```
The `have` approach is useful when you need to rewrite a hypothesis
rather than the goal — as you will see in Level 7.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
DisabledTheorem Nat.sum_range_choose
