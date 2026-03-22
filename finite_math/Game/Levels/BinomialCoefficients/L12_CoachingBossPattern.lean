import Game.Metadata

World "BinomialCoefficients"
Level 12

Title "Coaching: The Boss Pattern"

Introduction "
# Coaching for the Boss

The boss asks you to prove an identity about $\\binom{n+2}{2}$ by induction.
Here you'll practice the **exact same pattern** on a simpler statement.

Choosing $n + 1$ items from $n + 2$ equals $n + 2$ (you're just choosing
which one item to leave out). Multiplying both sides by $2$ gives:

$$2 \\cdot \\binom{n+2}{n+1} = 2(n+2)$$

**Proof plan** (identical to the boss pattern):
- **Base case** ($n = 0$): $2 \\cdot \\binom{2}{1} = 2 \\cdot 2$.
  Use `choose_one_right` to simplify.
- **Inductive step**: Expand with Pascal's identity, **distribute** the $2$
  with `mul_add`, simplify with `choose_self`, substitute the IH, close
  with `ring`.

The new move here is `mul_add`: it distributes `a * (b + c)` into
`a * b + a * c`. This is essential for the boss because after Pascal
peels off a sum, the leading factor of $2$ must be distributed before
the IH can fire.
"

/-- 2 * C(n+2, n+1) = 2 * (n+2): coaching for the boss induction pattern. -/
Statement (n : ℕ) : 2 * Nat.choose (n + 2) (n + 1) = 2 * (n + 2) := by
  Hint "This requires **induction** on `n`.
  The proof follows the same peel + distribute + IH + ring
  pattern as the boss."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case** (n = 0): The goal is `2 * Nat.choose 2 1 = 2 * 2`.
    Since C(2, 1) = 2 by `choose_one_right`, the rewrite closes
    the goal automatically."
    Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
    rw [Nat.choose_one_right]
  | succ n ih =>
    Hint "**Inductive step**: The goal is
    `2 * Nat.choose (n + 3) (n + 2) = 2 * (n + 3)`.

    Strategy (same as the boss):
    1. Expand with Pascal's identity (`choose_succ_succ`)
    2. Distribute the $2$ with `mul_add`
    3. Simplify `choose (n+2) (n+2)` with `choose_self`
    4. Substitute the IH
    5. Close with `ring`"
    Hint (hidden := true) "Try `rw [Nat.choose_succ_succ, mul_add, Nat.choose_self, ih]`
    then `ring`."
    rw [Nat.choose_succ_succ, mul_add, Nat.choose_self, ih]
    Hint "The goal is now a pure arithmetic identity. Use `ring`."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
$2 \\cdot \\binom{n+2}{n+1} = 2(n+2)$

You just practiced the **exact boss pattern**:
1. `induction n with` — set up the induction
2. `Nat.choose_succ_succ` — Pascal's identity peels off the sum
3. `mul_add` — distribute the leading factor over the sum
4. `Nat.choose_self` — simplify the boundary term
5. `ih` — substitute the induction hypothesis
6. `ring` — close the polynomial identity

This is the **peel + distribute + simplify + IH + ring** skeleton.
The boss uses the same skeleton with slightly different boundary theorems
(`choose_one_right` instead of `choose_self`).

**Key new move**: `mul_add` distributes multiplication over addition:
`a * (b + c) = a * b + a * c`. Without this, the IH can't fire because
`2 * Nat.choose ...` is trapped inside `2 * (... + ...)`.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
