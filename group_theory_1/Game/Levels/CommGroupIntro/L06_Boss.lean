import Game.Metadata

World "CommGroupIntro"
Level 6

Title "Boss — Power of a Product"

Introduction
"
In a commutative group, the power of a product is the product of
the powers:

`(a * b) ^ n = a ^ n * b ^ n`

This is **false** in a general group — the proof fundamentally
needs commutativity to rearrange factors in the induction step.

Use induction on `n`. Every tool you need has been introduced in
this world:

- `pow_zero` and `pow_succ` for unfolding powers
- `induction` for the inductive structure
- `mul_mul_mul_comm` for the rearrangement in the induction step
"

/-- `mul_pow` says `(a * b) ^ n = a ^ n * b ^ n` in a commutative
group (or commutative monoid).

The power of a product equals the product of the powers. This
requires commutativity — it is false in general groups.

In a non-commutative group, `(a * b) ^ 2 = a * b * a * b`, which
is NOT `a * a * b * b = a ^ 2 * b ^ 2` unless `a` and `b` commute. -/
TheoremDoc mul_pow as "mul_pow" in "Power"

NewTheorem mul_pow

TheoremTab "Power"

Statement (G : Type*) [CommGroup G] (a b : G) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  Hint "Use `induction n with` to set up the base case and
  induction step."
  induction n with
  | zero =>
    Hint "**Base case**: `(a * b) ^ 0 = a ^ 0 * b ^ 0`. Unfold
    all three powers with `pow_zero`, then use `one_mul` to simplify
    `1 * 1`."
    Hint (hidden := true) "`rw [pow_zero, pow_zero, pow_zero, one_mul]`"
    rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ n ih =>
    Hint "**Induction step**: the goal is
    `(a * b) ^ ({n} + 1) = a ^ ({n} + 1) * b ^ ({n} + 1)` with
    `ih : (a * b) ^ {n} = a ^ {n} * b ^ {n}`.

    **Plan**:
    1. Unfold all three `^ ({n} + 1)` using `pow_succ`
    2. Apply `ih` to replace `(a * b) ^ {n}` with `a ^ {n} * b ^ {n}`
    3. Use `mul_mul_mul_comm` to rearrange the four factors"
    Hint (hidden := true) "The full induction step in one line:
    `rw [pow_succ, pow_succ, pow_succ, ih, mul_mul_mul_comm]`

    After the three `pow_succ` rewrites and `ih`, the goal becomes
    `a ^ {n} * b ^ {n} * (a * b) = a ^ {n} * a * (b ^ {n} * b)`.
    The interchange law `mul_mul_mul_comm` rearranges the left side
    to match.

    Alternatively, you can write a `calc` proof handling each
    rewrite as a separate step."
    Branch
      -- calc proof
      calc (a * b) ^ (n + 1)
          _ = (a * b) ^ n * (a * b)      := by rw [pow_succ]
          _ = a ^ n * b ^ n * (a * b)    := by rw [ih]
          _ = a ^ n * a * (b ^ n * b)    := by rw [mul_mul_mul_comm]
          _ = a ^ (n + 1) * (b ^ n * b)  := by rw [← pow_succ]
          _ = a ^ (n + 1) * b ^ (n + 1)  := by rw [← pow_succ]
    rw [pow_succ, pow_succ, pow_succ, ih, mul_mul_mul_comm]

Conclusion
"
Congratulations on completing **Commutative Groups**!

You proved the **power-of-a-product** theorem by induction. The
key step was the interchange law `mul_mul_mul_comm`, which
rearranged `a ^ n * b ^ n * (a * b)` into `a ^ n * a * (b ^ n * b)`.
This rearrangement is exactly where commutativity was needed — in
a non-commutative group, you cannot swap `b ^ n` past `a`.

Your new toolkit from this world:

| Theorem | Statement |
|---------|-----------|
| `mul_comm` | `a * b = b * a` |
| `mul_left_comm` | `a * (b * c) = b * (a * c)` |
| `mul_mul_mul_comm` | `a * b * (c * d) = a * c * (b * d)` |
| `pow_zero` | `a ^ 0 = 1` |
| `pow_succ` | `a ^ (n + 1) = a ^ n * a` |
| `pow_one` | `a ^ 1 = a` |
| `one_pow` | `1 ^ n = 1` |
| `mul_pow` | `(a * b) ^ n = a ^ n * b ^ n` |

And the re-introduced tactic: `induction`.

**Why commutativity matters**: the equation `(a * b) ^ n = a ^ n * b ^ n`
is a litmus test for commutativity. If this holds for all `a`, `b`,
and `n = 2`, then the group must be abelian. Here's why:
expand `(a * b) ^ 2 = a * b * a * b` and `a ^ 2 * b ^ 2 = a * a * b * b`.
Setting them equal gives `a * b * a * b = a * a * b * b`. Cancel
`a` on the left and `b` on the right to get `b * a = a * b`.
So a single power identity forces full commutativity. You'll see the
converse direction — measuring *how far* a group is from being abelian —
when you study commutator subgroups.

Next up: subgroups — where you'll learn what it means for a subset
of a group to form a group in its own right.
"
