import Game.Metadata

World "PsetCombinatorics"
Level 3

Title "Weighted Alternating Sum Over Z"

Introduction "
# The Identity Machine Over $\\mathbb{Z}$

In BinomialTheorem, you used the **specialize-simplify-rewrite**
pattern to derive identities from `add_pow_nat` (over $\\mathbb{N}$).

But you also learned to specialize over $\\mathbb{Z}$, using
`add_pow` (not `add_pow_nat`) to allow negative values. The
alternating sum identity (BinomialTheorem Level 15) used $x = -1, y = 1$.

Now try a different $\\mathbb{Z}$ specialization: $x = -1, y = 3$.

$$\\sum_{m=0}^{n} (-1)^m \\cdot 3^{n-m} \\cdot \\binom{n}{m} = 2^n$$

**Key differences from $\\mathbb{N}$ specializations**:
- Use `add_pow` (not `add_pow_nat`) — we need $\\mathbb{Z}$ for $x = -1$
- The coercion `\\uparrow(\\text{choose } n\\ m)` appears automatically
  (Lean casts $\\mathbb{N}$ values to $\\mathbb{Z}$)
- The LHS simplification uses `omega` for $\\mathbb{Z}$ arithmetic

**Strategy**:
1. `have h := add_pow (-1 : \\mathbb{Z}) 3 n`
2. Simplify the LHS: $(-1 + 3) = 2$ via `omega`
3. Rewrite and close
"

/-- The weighted alternating sum with x = -1, y = 3 over Z. -/
Statement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m * (3 : ℤ) ^ (n - m) * ↑(Nat.choose n m) =
    (2 : ℤ) ^ n := by
  Hint "Start by specializing `add_pow` (not `add_pow_nat`!) to
  `x = -1, y = 3` over ℤ."
  Hint (hidden := true) "Try `have h := add_pow (-1 : ℤ) 3 n`."
  have h := add_pow (-1 : ℤ) 3 n
  Hint "Now `h` says `(-1 + 3)^n = ∑ m, (-1)^m * 3^(n-m) * ↑(choose n m)`.

  The right side of `h` matches the goal's left side. You need to
  simplify the left side: `(-1 : ℤ) + 3 = 2`.

  Establish this with `omega` and rewrite."
  Hint (hidden := true) "Try:
  `have h0 : (-1 : ℤ) + 3 = 2 := by omega`
  `rw [h0] at h`"
  have h0 : (-1 : ℤ) + 3 = 2 := by omega
  rw [h0] at h
  Hint "Now `h` says `(2 : ℤ)^n = ∑ m, (-1)^m * 3^(n-m) * ↑(choose n m)`.
  The goal is `∑ ... = (2 : ℤ)^n`. Flip `h` and close."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion "
You proved the $\\mathbb{Z}$ specialization $x = -1, y = 3$.

The key differences from $\\mathbb{N}$: use `add_pow` (not
`add_pow_nat`), `omega` for $\\mathbb{Z}$ arithmetic, and
the coercion `\\uparrow(\\text{choose})` appears automatically.
Each specialization evaluates $(x + y)^n$ at specific values —
this one gives $((-1) + 3)^n = 2^n$.
"

/-- `Int.alternating_sum_range_choose` gives the alternating row sum
`∑ m, (-1)^m * choose n m = 0` (for `n > 0`).

We disable it to prevent one-shotting the weighted sum identity.
The student should derive this specialization from `add_pow` directly.
-/
TheoremDoc Int.alternating_sum_range_choose as "Int.alternating_sum_range_choose" in "Choose"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Int.alternating_sum_range_choose
