import Game.Metadata

World "BinomialTheorem"
Level 13

Title "Working Over Integers"

Introduction "
# Beyond Natural Numbers: $\\mathbb{Z}$

All specializations so far used natural numbers ($x = 1$, $x = 2$).
But `add_pow` works over any commutative semiring — including the
integers $\\mathbb{Z}$.

Over $\\mathbb{Z}$, you can set $x = -1$. Then $(-1 + 1) = 0$, and
the binomial theorem gives something surprising: the enormous
alternating sum $\\sum (-1)^m \\binom{n}{m}$ collapses to $0^n$.

Before tackling that identity, you need two tools for simplifying
expressions over $\\mathbb{Z}$:

**`zero_pow`**: For $n \\geq 1$, $0^n = 0$.
```
zero_pow (h : n ≠ 0) : (0 : M) ^ n = 0
```

**`omega`**: You already know `omega` from earlier worlds. Here
you will use it to prove arithmetic facts like $(-1) + 1 = 0$
and $n \\neq 0$ (from $1 \\leq n$).

**Your task**: Prove that $(-1 + 1)^n = 0$ for $n \\geq 1$.
This is the left-hand side of the alternating sum identity.
"

/-- Powers of (-1 + 1) are zero for positive exponents. -/
Statement (n : ℕ) (hn : 1 ≤ n) :
    ((-1 : ℤ) + 1) ^ n = 0 := by
  Hint "The expression `(-1 : ℤ) + 1` equals `0`. Establish this as
  a rewrite lemma using `have h0 : (-1 : ℤ) + 1 = 0 := by omega`."
  Hint (hidden := true) "Try `have h0 : (-1 : ℤ) + 1 = 0 := by omega`."
  have h0 : (-1 : ℤ) + 1 = 0 := by omega
  Hint "Good — now rewrite `(-1 + 1)` to `0` in the goal."
  Hint (hidden := true) "Try `rw [h0]`."
  rw [h0]
  Hint "The goal is `(0 : ℤ) ^ n = 0`. Since `n ≥ 1`, we have `n ≠ 0`,
  so `zero_pow` applies. Use `exact zero_pow (by omega)` — the
  `by omega` proves `n ≠ 0` from the hypothesis `hn : 1 ≤ n`."
  Hint (hidden := true) "Try `exact zero_pow (by omega)`."
  exact zero_pow (by omega)

Conclusion "
Three steps: `have h0`, `rw [h0]`, `exact zero_pow (by omega)`.

**New tools**:
- `zero_pow (h : n ≠ 0) : 0 ^ n = 0` — any positive power of zero
  is zero. The argument `h` proves the exponent is nonzero.
- `omega` as a sub-proof: `by omega` can prove simple arithmetic
  facts like `(-1 : ℤ) + 1 = 0` and `n ≠ 0` (from `1 ≤ n`).

**Why ℤ?** Over $\\mathbb{N}$, there is no $-1$, so you cannot
specialize `add_pow` to $x = -1$. Working over $\\mathbb{Z}$ unlocks
negative values, which produce the **alternating sum** identity.
This illustrates a broader Lean lesson: **the type you work in
determines what operations are available**. Over $\\mathbb{N}$, you
have addition and multiplication but not subtraction (it truncates).
Over $\\mathbb{Z}$, you gain subtraction and negation, which lets
you express alternating sums. Choosing the right type is part of
setting up a proof — sometimes the mathematics forces the choice.

**Why $n \\geq 1$?** This level requires `hn : 1 \\leq n`. Why?
Because $0^0 = 1$ by convention, not $0$. If $n = 0$, then
$(-1 + 1)^0 = 0^0 = 1$, not $0$. The hypothesis $n \\geq 1$ is
what makes $0^n = 0$ true. The next level uses the same hypothesis
for the alternating sum identity: at $n = 0$, the sum has only
one term $(-1)^0 \\binom{0}{0} = 1 \\neq 0$.

**Type coercion `\\uparrow`**: The next level works over $\\mathbb{Z}$,
but `Nat.choose n m` returns a natural number. When a natural
number appears in an integer expression, Lean automatically inserts
the coercion `\\uparrow(Nat.choose n m)` to cast it to $\\mathbb{Z}$.
You do not need to type `\\uparrow` yourself — Lean adds it. But you
will see it in the goal display. It does not affect how `rw` works:
you can still rewrite through the coercion normally.

**Preview**: In Level 14, you will verify a concrete case of the
alternating sum ($1 - 4 + 6 - 4 + 1 = 0$). Then in Level 15 (the
boss), you will combine this $\\mathbb{Z}$-specific reasoning with
the specialize-simplify-rewrite pattern to prove:

$$\\sum_{m=0}^{n} (-1)^m \\binom{n}{m} = 0$$

The enormous alternating sum of an entire row of Pascal's triangle
collapses to zero — the most surprising consequence of the binomial
theorem.
"

/-- `zero_pow` states that `0 ^ n = 0` when `n ≠ 0`.

## Syntax
```
exact zero_pow h
rw [zero_pow h]
```
where `h : n ≠ 0` is a proof that the exponent is nonzero.

## When to use it
When the goal or hypothesis contains `0 ^ n` and you know `n ≥ 1`
(equivalently, `n ≠ 0`). Often combined with `by omega` to
produce the proof: `zero_pow (by omega)`.

## Example
```
-- Given hn : 1 ≤ n
exact zero_pow (by omega)  -- closes goal (0 : ℤ) ^ n = 0
```
-/
TheoremDoc zero_pow as "zero_pow" in "Algebra"

TheoremTab "Algebra"
NewTheorem zero_pow

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
