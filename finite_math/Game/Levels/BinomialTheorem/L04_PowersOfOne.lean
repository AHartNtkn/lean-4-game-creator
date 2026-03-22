import Game.Metadata

World "BinomialTheorem"
Level 4

Title "Simplifying Powers of One"

Introduction "
# Powers of One: `one_pow` and `one_mul`

When you specialize the binomial theorem to `x = 1` or `y = 1`,
the summand acquires terms like `1 ^ m` and `1 * c`. These need
to be simplified before you can recognize the resulting identity.

Two lemmas do the job:

**`one_pow`**: $(1)^n = 1$ for any natural number $n$.
```
one_pow (n : ℕ) : (1 : M) ^ n = 1
```

**`one_mul`**: $1 \\cdot a = a$.
```
one_mul (a : M) : 1 * a = a
```

There is also **`mul_one`**: $a \\cdot 1 = a$.
```
mul_one (a : M) : a * 1 = a
```

The distinction: `one_mul` removes a leading `1 *`, while
`mul_one` removes a trailing `* 1`.

**Your task**: Simplify `1 ^ k * 1 ^ j * c` down to `c` using
these three lemmas. This is the exact pattern you will need
when specializing `add_pow` to `x = 1, y = 1`.
"

/-- Simplify products involving powers of 1 down to the remaining factor. -/
Statement (k j c : ℕ) : 1 ^ k * 1 ^ j * c = c := by
  Hint "The expression has two `1 ^ _` terms. Use `rw [one_pow]`
  to simplify the first one — `1 ^ k` becomes `1`."
  rw [one_pow]
  Hint "Good — now the expression starts with `1 * 1 ^ j * c`.
  Apply `rw [one_pow]` again to simplify `1 ^ j`."
  Hint (hidden := true) "Try `rw [one_pow]`."
  rw [one_pow]
  Hint "The expression is now `1 * 1 * c`. The leading `1 *`
  can be removed with `rw [one_mul]` — it matches `1 * (1 * c)`
  after the first `one_mul` removes the outer `1 *`.

  Actually, since `*` is left-associative, `1 * 1 * c` parses as
  `(1 * 1) * c`. So `rw [one_mul]` first simplifies `1 * 1` to `1`,
  leaving `1 * c`."
  Hint (hidden := true) "Try `rw [one_mul]` twice, or `rw [one_mul, one_mul]`."
  rw [one_mul, one_mul]

Conclusion "
Four rewrites: `one_pow, one_pow, one_mul, one_mul`.

You can chain them: `rw [one_pow, one_pow, one_mul, one_mul]`.

**The pattern**: When `x = 1` in the binomial theorem, each summand
has the factor `1 ^ m`. When `y = 1`, each summand has `1 ^ (n - m)`.
Specializing both gives `1 ^ m * 1 ^ (n - m) * choose n m`, which
simplifies to `choose n m` by this exact sequence of rewrites.

**`one_mul` vs `mul_one`**:
- `one_mul : 1 * a = a` — removes a leading `1 *`
- `mul_one : a * 1 = a` — removes a trailing `* 1`

You will use `mul_one` in Level 9 when the trailing factor is `1`.
"

/-- `one_pow` states that `(1 : M) ^ n = 1`.

Any power of 1 is 1.

## Syntax
```
rw [one_pow]
```

## When to use it
When you see `1 ^ n` in the goal or a hypothesis and want to
simplify it to `1`. Common after specializing `add_pow` to
`x = 1` or `y = 1`.
-/
TheoremDoc one_pow as "one_pow" in "Algebra"

/-- `one_mul` states that `1 * a = a`.

## Syntax
```
rw [one_mul]
```

## When to use it
When the goal has `1 * a` and you want to simplify to `a`.
-/
TheoremDoc one_mul as "one_mul" in "Algebra"

/-- `mul_one` states that `a * 1 = a`.

## Syntax
```
rw [mul_one]
```

## When to use it
When the goal has `a * 1` and you want to simplify to `a`.
This is the right-hand version of `one_mul`.
-/
TheoremDoc mul_one as "mul_one" in "Algebra"

TheoremTab "Algebra"
NewTheorem one_pow one_mul mul_one

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
DisabledTheorem Nat.sum_range_choose
