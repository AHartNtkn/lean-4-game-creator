import Game.Metadata

World "CommGroupIntro"
Level 4

Title "Powers of the Identity"

Introduction
"
What is `1 ^ n`? Multiplying the identity by itself any number of
times gives the identity: `1 ^ n = 1` for all `n`.

To prove this, you need **induction on `n`** — a technique you
already know from the Natural Number Game. The `induction` tactic
splits the proof into two goals:

1. **Base case** (`n = 0`): prove `1 ^ 0 = 1`
2. **Induction step** (`n → n + 1`): assuming `ih : 1 ^ n = 1`,
   prove `1 ^ (n + 1) = 1`

Write `induction n with` to begin. Lean will create two goals
named `zero` and `succ n ih`.
"

/-- The `induction` tactic performs induction on a natural number
(or any inductive type).

```
induction n with
| zero => -- prove the base case (n = 0)
| succ n ih => -- prove the step case, with ih as the hypothesis
```

`ih` is the **induction hypothesis**: the statement for `n` that
you can use to prove the statement for `n + 1`. -/
TacticDoc induction

/-- `one_pow` says `1 ^ n = 1` for any natural number `n` — the
identity raised to any power is the identity. -/
TheoremDoc one_pow as "one_pow" in "Power"

NewTactic induction
NewTheorem one_pow

TheoremTab "Power"

Statement (G : Type*) [Group G] (n : ℕ) : (1 : G) ^ n = 1 := by
  Hint "Use `induction n with` to split into base case and
  induction step. The syntax is:
  ```
  induction n with
  | zero => sorry
  | succ n ih => sorry
  ```
  Replace each `sorry` with the actual proof."
  induction n with
  | zero =>
    Hint "**Base case**: the goal is `1 ^ 0 = 1`. Which power
    theorem handles `_ ^ 0`?"
    rw [pow_zero]
  | succ n ih =>
    Hint "**Induction step**: the goal is `1 ^ ({n} + 1) = 1` and
    you have `ih : 1 ^ {n} = 1`.

    First unfold `1 ^ ({n} + 1)` using `pow_succ`. Then use `ih`
    to simplify `1 ^ {n}` to `1`. Finally, `one_mul` handles `1 * 1`."
    Hint (hidden := true) "`rw [pow_succ, ih, one_mul]` closes the
    goal in one line."
    rw [pow_succ, ih, one_mul]

Conclusion
"
Induction on natural numbers — the same technique from the
Natural Number Game, now applied to group theory.

The **induction-on-powers** template:
1. `rw [pow_succ]` to unfold `a ^ (n + 1)` into `a ^ n * a`
2. `rw [ih]` to replace the `a ^ n` part using the induction hypothesis
3. Clean up with group axioms (here it was `one_mul`)

Step 3 varies — the identity cleanup here was trivial, but in harder
proofs the cleanup is where the real work happens. The boss will
use `mul_mul_mul_comm` for step 3 instead of `one_mul`.
"
