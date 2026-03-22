import Game.Metadata

World "SummationFormulas"
Level 10

Title "Computing a Factorial"

Introduction "
# Meet the Factorial

The **factorial** $n!$ counts the number of ways to arrange $n$ objects
in a line (permutations). It is defined recursively:
- $0! = 1$ (there is exactly one way to arrange zero objects)
- $(n+1)! = (n+1) \\cdot n!$

In Lean:
```
Nat.factorial_zero : Nat.factorial 0 = 1
Nat.factorial_succ : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n
```

**Your task**: Show that $3! = 3 \\cdot (2 \\cdot (1 \\cdot 1))$ by unfolding
the recursive definition step by step. Each application of `factorial_succ`
peels off one factor, and `factorial_zero` reaches the base case.
The RHS shows the recursive structure explicitly.
"

/-- `Nat.factorial n` (written `n !` or `Nat.factorial n`) is the
product of all positive integers up to `n`.

## Definition
- `Nat.factorial 0 = 1`
- `Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`

## Key lemmas
- `Nat.factorial_zero : Nat.factorial 0 = 1`
- `Nat.factorial_succ : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`

## Combinatorial meaning
`n!` counts the number of permutations (orderings) of `n` distinct objects.
-/
DefinitionDoc Nat.factorial as "Nat.factorial"

/-- `Nat.factorial_zero` states that `Nat.factorial 0 = 1`.

## Syntax
```
rw [Nat.factorial_zero]
```

## When to use it
In base cases of inductive proofs about factorials.
-/
TheoremDoc Nat.factorial_zero as "Nat.factorial_zero" in "Nat"

/-- `Nat.factorial_succ` states that
`Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`.

## Syntax
```
rw [Nat.factorial_succ]
```

## When to use it
In inductive steps to unfold the factorial of a successor.
-/
TheoremDoc Nat.factorial_succ as "Nat.factorial_succ" in "Nat"

/-- Three factorial equals 3 * (2 * (1 * 1)), showing the recursive structure. -/
Statement : Nat.factorial 3 = 3 * (2 * (1 * 1)) := by
  Hint "Unfold the factorial step by step using `Nat.factorial_succ`.
  Each application peels off one factor:
  $3! = 3 \\cdot 2!$, then $2! = 2 \\cdot 1!$, then $1! = 1 \\cdot 0!$."
  Hint (hidden := true) "Try `rw [Nat.factorial_succ]`."
  rw [Nat.factorial_succ]
  Hint "Good — you've unfolded $3! = 3 \\cdot 2!$. Now unfold $2!$."
  Hint (hidden := true) "Try `rw [Nat.factorial_succ]` again."
  rw [Nat.factorial_succ]
  Hint "Now unfold $1!$ to reach $0!$."
  Hint (hidden := true) "Try `rw [Nat.factorial_succ]`."
  rw [Nat.factorial_succ]
  Hint "You've reached `3 * (2 * (1 * Nat.factorial 0))`.
  Use `Nat.factorial_zero` to replace $0!$ with $1$."
  Hint (hidden := true) "Try `rw [Nat.factorial_zero]`."
  rw [Nat.factorial_zero]

Conclusion "
You computed $3! = 3 \\cdot 2 \\cdot 1 \\cdot 1 = 6$.

The recursive unfolding makes the structure visible:
$$3! = 3 \\cdot 2! = 3 \\cdot 2 \\cdot 1! = 3 \\cdot 2 \\cdot 1 \\cdot 0! = 3 \\cdot 2 \\cdot 1 \\cdot 1 = 6$$

For reference: $4! = 24$, $5! = 120$, $10! = 3628800$. Factorials
grow *very* fast — faster than any polynomial or exponential in a
fixed base.

In the next level, you'll prove the *general* connection between
the factorial and big-operator products.
"

NewTheorem Nat.factorial_zero Nat.factorial_succ
NewDefinition Nat.factorial

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id
