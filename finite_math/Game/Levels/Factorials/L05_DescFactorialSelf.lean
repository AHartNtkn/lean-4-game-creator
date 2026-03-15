import GameServer.Commands
import Mathlib

World "Factorials"
Level 5

Title "Descending all the way"

Introduction
"
# The key identity: $n^{\\underline{n}} = n!$

When the descending factorial descends all the way — taking
all $n$ terms from $n$ — you get the ordinary factorial.
Intuitively: $n^{\\underline{n}} = n(n-1)\\cdots 2 \\cdot 1 = n!$.

## The helper lemma

To prove this by induction, you will need a new lemma that
relates the descending factorial of $n+1$ to that of $n$:

```
Nat.succ_descFactorial_succ (n k : ℕ) :
  (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
```

This says: $(n+1)^{\\underline{k+1}} = (n+1) \\cdot n^{\\underline{k}}$.

Compare this with `Nat.descFactorial_succ`, which uses subtraction:

```
n.descFactorial (k + 1) = (n - k) * n.descFactorial k
```

The `succ_descFactorial_succ` version avoids subtraction entirely,
which makes induction proofs cleaner.

## Your task

Prove `n.descFactorial n = Nat.factorial n` by induction on `n`.
"

/-- The descending factorial n^{\\underline{n}} equals n!. -/
Statement (n : ℕ) : Nat.descFactorial n n = Nat.factorial n := by
  Hint "Start with `induction n with` to prove this by induction."
  induction n with
  | zero =>
    Hint "In the base case, both sides equal `1`. Use
    `rw [Nat.descFactorial_zero, Nat.factorial_zero]`."
    Hint (hidden := true) "Try `rw [Nat.descFactorial_zero, Nat.factorial_zero]`."
    rw [Nat.descFactorial_zero, Nat.factorial_zero]
  | succ n ih =>
    Hint "In the inductive step, the goal is:

    `(n + 1).descFactorial (n + 1) = (n + 1).factorial`

    Use `rw [Nat.succ_descFactorial_succ]` to rewrite the left side to
    `(n + 1) * n.descFactorial n`."
    Hint (hidden := true) "Try `rw [Nat.succ_descFactorial_succ]`."
    rw [Nat.succ_descFactorial_succ]
    Hint "Now the goal is `(n + 1) * n.descFactorial n = (n + 1).factorial`.

    Apply the inductive hypothesis `ih : n.descFactorial n = n.factorial`
    with `rw [ih]`."
    Hint (hidden := true) "Try `rw [ih]`."
    rw [ih]
    Hint "The goal is now `(n + 1) * n.factorial = (n + 1).factorial`.

    This is exactly `Nat.factorial_succ` read right-to-left.
    Use `rw [Nat.factorial_succ]` to close it."
    Hint (hidden := true) "Try `rw [Nat.factorial_succ]`."
    rw [Nat.factorial_succ]

Conclusion
"
You proved the key identity $n^{\\underline{n}} = n!$ by induction.

## The proof structure

- **Base case**: $0^{\\underline{0}} = 1 = 0!$
- **Inductive step**:
  $(n+1)^{\\underline{n+1}} = (n+1) \\cdot n^{\\underline{n}} = (n+1) \\cdot n! = (n+1)!$

The three rewrites in the inductive step correspond to three facts:
1. `succ_descFactorial_succ`: peels off the top factor
2. `ih`: applies the inductive hypothesis
3. `factorial_succ`: recognizes $(n+1) \\cdot n!$ as $(n+1)!$

## Transfer moment

On paper, you would write this proof almost identically:

> *Proof by induction on $n$.*
> *Base case*: $0^{\\underline{0}} = 1 = 0!$. $\\checkmark$
> *Inductive step*: Assume $n^{\\underline{n}} = n!$. Then
> $(n+1)^{\\underline{n+1}} = (n+1) \\cdot n^{\\underline{n}}
> = (n+1) \\cdot n! = (n+1)!$. $\\square$

Each equality in the paper proof corresponds to exactly one `rw`
step in the Lean proof.

## What comes next

The next level gives a preview of how factorials connect to
counting permutations.
"

/-- `Nat.succ_descFactorial_succ` states that
`(n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k`.

This rewrites the descending factorial by peeling off the top
factor $(n+1)$. Unlike `descFactorial_succ`, this version avoids
subtraction, making it ideal for induction proofs. -/
TheoremDoc Nat.succ_descFactorial_succ as "Nat.succ_descFactorial_succ" in "Nat"

NewTheorem Nat.succ_descFactorial_succ
DisabledTactic trivial decide native_decide simp aesop simp_all
