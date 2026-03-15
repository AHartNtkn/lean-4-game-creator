import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 10

Title "Boss: a combined binomial identity"

Introduction
"
# Boss: Derive a Binomial Identity

Prove the following identity by specializing the binomial theorem:

$$\\sum_{k=0}^{n} (-1)^k \\cdot 2^{n-k} \\cdot \\binom{n}{k} = 1$$

## Strategy

This identity comes from setting $x = -1$ and $y = 2$ in the
binomial theorem:

$$(x + y)^n = \\sum_{k=0}^{n} x^k \\cdot y^{n-k} \\cdot \\binom{n}{k}$$

With $x = -1, y = 2$:

$$(-1 + 2)^n = 1^n = 1 = \\sum_{k=0}^{n} (-1)^k \\cdot 2^{n-k} \\cdot \\binom{n}{k}$$

## Proof plan

1. Apply `add_pow` with `x = -1, y = 2` to get `h : (-1 + 2) ^ n = ∑ ...`
2. Simplify `(-1 + 2)` to `1` using `ring`
3. Simplify `1 ^ n` to `1` using `one_pow`
4. Conclude from symmetry

## Concrete check

For $n = 3$:
$$(-1)^0 \\cdot 2^3 \\cdot 1 + (-1)^1 \\cdot 2^2 \\cdot 3 + (-1)^2 \\cdot 2^1 \\cdot 3 + (-1)^3 \\cdot 2^0 \\cdot 1$$
$$= 8 - 12 + 6 - 1 = 1 \\quad ✓$$
"

/-- A combined binomial identity: ∑ (-1)^k * 2^(n-k) * C(n,k) = 1. -/
Statement (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * 2 ^ (n - k) * ↑(Nat.choose n k) = 1 := by
  Hint "**Step 1**: Apply the binomial theorem with `x = -1` and `y = 2`.

  Use `have h := add_pow (-1 : ℤ) 2 n` to introduce the binomial
  expansion as a hypothesis."
  Hint (hidden := true) "Try `have h := add_pow (-1 : ℤ) 2 n`."
  have h := add_pow (-1 : ℤ) 2 n
  Hint "Good! You have:
  `h : (-1 + 2) ^ n = ∑ m ∈ Finset.range (n + 1), (-1) ^ m * 2 ^ (n - m) * ↑(Nat.choose n m)`

  **Step 2**: Simplify `(-1 + 2)` to `1` in `h`.

  Use `have h2 : (-1 : ℤ) + 2 = 1 := by ring` to establish the
  simplification, then `rw [h2] at h`."
  Hint (hidden := true) "Try:
  ```
  have h2 : (-1 : ℤ) + 2 = 1 := by ring
  rw [h2] at h
  ```"
  have h2 : (-1 : ℤ) + 2 = 1 := by ring
  rw [h2] at h
  Hint "**Step 3**: Now `h : 1 ^ n = ∑ ...`. Simplify `1 ^ n` to `1`.

  Try `rw [one_pow] at h`."
  Hint (hidden := true) "Try `rw [one_pow] at h`."
  rw [one_pow] at h
  Hint "**Step 4**: Now `h : 1 = ∑ ...` and the goal is `∑ ... = 1`.

  These are the same equation, just reversed. Use `exact h.symm` or
  `linarith`."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion
"
Congratulations on completing the **Binomial Theorem** world!

## The proof structure

You derived an identity by *specializing* the binomial theorem:

1. **Apply** `add_pow` at $x = -1, y = 2$
2. **Simplify** $(-1 + 2) = 1$ using `ring`
3. **Simplify** $1^n = 1$ using `one_pow`
4. **Conclude** by `h.symm`

This is a general technique: many binomial identities arise by
plugging specific values into the binomial theorem.

## What you learned in this world

| Level | Topic |
|-------|-------|
| L01 | The binomial theorem (`add_pow`) |
| L02 | `push_cast` for handling casts |
| L03 | Binomial theorem in `ℤ` |
| L04 | Row sum from the binomial theorem ($x = y = 1$) |
| L05 | Row sum identity (`Nat.sum_range_choose`) |
| L06 | Vandermonde's identity (`Nat.add_choose_eq`) |
| L07 | Vandermonde: concrete computation |
| L08 | Alternating sum identity |
| L09 | Transfer: stating the theorem on paper |
| L10 | Boss: deriving an identity by specialization |

## Transfer: the method of specialization

On paper:

> *To prove $\\sum (-1)^k 2^{n-k} \\binom{n}{k} = 1$, set $x = -1$
> and $y = 2$ in the binomial theorem:*
> $$(-1 + 2)^n = \\sum_{k=0}^{n} (-1)^k \\cdot 2^{n-k} \\cdot \\binom{n}{k}$$
> *Since $-1 + 2 = 1$ and $1^n = 1$, the identity follows. $\\square$*

This \"plug in and simplify\" strategy is how many combinatorial
identities are proved algebraically.

## Key tactics and lemmas

**Tactics**: `push_cast` (new), `have`, `rw`, `exact`, `ring`, `omega`

**Lemmas**:
- `add_pow` — the binomial theorem
- `Nat.sum_range_choose` — row sum $= 2^n$
- `Nat.add_choose_eq` — Vandermonde's identity
- `Int.alternating_sum_range_choose_of_ne` — alternating sum $= 0$
- `one_pow` — $1^n = 1$

## What comes next

The next world applies these identities in problem-set form.
"

/-- `one_pow` states that `1 ^ n = 1` for any `n : ℕ`.

Any power of 1 equals 1. This is useful for simplifying the binomial
theorem after substituting `x = 1` or `y = 1`. -/
TheoremDoc one_pow as "one_pow" in "Nat"

NewTheorem one_pow
DisabledTactic trivial decide native_decide simp aesop simp_all
