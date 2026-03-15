import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 7

Title "Boss: every permutation of Fin 3 has σ^6 = 1"

Introduction
"
# Boss: A Property of All Permutations of `Fin 3`

Time to integrate the ideas from this world. You will prove two facts:

1. **Counting**: The symmetric group $S_3$ has exactly 6 elements.
2. **Exponent**: Every permutation $\\sigma \\in S_3$ satisfies
   $\\sigma^6 = \\mathrm{id}$.

## Strategy

**Part 1** reviews the counting connection from Level 5:
use `Fintype.card_perm` and `Fintype.card_fin`, then compute $3! = 6$.

**Part 2** uses a beautiful theorem from group theory:

```
pow_card_eq_one : x ^ Fintype.card G = 1
```

This is a consequence of **Lagrange's theorem**: in any finite group $G$,
every element $x$ satisfies $x^{|G|} = 1$ (the identity).

Since $|S_3| = 6$, we get $\\sigma^6 = 1$ for every $\\sigma \\in S_3$.

The proof of Part 2:
1. Show that `Fintype.card (Equiv.Perm (Fin 3)) = 6` (same as Part 1).
2. Rewrite `6` as `Fintype.card (Equiv.Perm (Fin 3))`.
3. Apply `pow_card_eq_one`.

## Your task

Prove both parts as a conjunction.
"

/-- The symmetric group S₃ has 6 elements, and every element raised to the 6th power is the identity. -/
Statement : Fintype.card (Equiv.Perm (Fin 3)) = 6 ∧
    ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "**Part 1**: Use `Fintype.card_perm`, `Fintype.card_fin`, and the
    factorial recursion to compute $|S_3| = 3! = 6$.

    Try:
    ```
    rw [Fintype.card_perm, Fintype.card_fin]
    rw [Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_zero]
    ```"
    Hint (hidden := true) "Try `rw [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_zero]`."
    rw [Fintype.card_perm, Fintype.card_fin]
    rw [Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_zero]
  · Hint "**Part 2**: Introduce `σ` with `intro σ`.

    Then use `have` to establish that `Fintype.card (Equiv.Perm (Fin 3)) = 6`,
    rewrite `6` using this fact, and apply `pow_card_eq_one`."
    intro σ
    Hint "First, establish the cardinality fact:
    ```
    have h : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      rw [Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ, Nat.factorial_zero]
    ```

    Then `rw [← h]` to replace `6` with the cardinality, and
    `exact pow_card_eq_one` to finish."
    Hint (hidden := true) "The key step is `rw [← h]` followed by
    `exact pow_card_eq_one`, where `h` proves the cardinality equals 6."
    have h : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      rw [Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ, Nat.factorial_zero]
    rw [← h]
    exact pow_card_eq_one

Conclusion
"
Congratulations on completing the **Permutations of Finite Types** world!

You proved that every element of $S_3$ satisfies $\\sigma^6 = 1$, combining:
- **Counting** (`card_perm` + `card_fin` + factorial computation)
- **Group theory** (`pow_card_eq_one` — Lagrange's theorem)

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| Permutation definition (`Equiv.Perm`) | L01 | `Equiv.swap_apply_left` |
| Concrete swap evaluation | L02 | `Equiv.swap_apply_of_ne_of_ne` |
| Composition of permutations | L03 | `Equiv.Perm.mul_def`, `Equiv.trans_apply` |
| Identity permutation | L04 | `Equiv.Perm.one_def` |
| Counting permutations | L05 | `Fintype.card_perm` |
| `List.Perm` vs `Equiv.Perm` | L06 | `List.Perm.swap` |
| Group-theoretic property | L07 | `pow_card_eq_one` |

## Transfer moment

In ordinary mathematics, you would say: \"By Lagrange's theorem, every
element of a finite group $G$ satisfies $g^{|G|} = e$. Since $|S_3| = 6$,
every permutation $\\sigma \\in S_3$ satisfies $\\sigma^6 = \\mathrm{id}$.\"

In Lean, this argument splits into two pieces:
1. A **counting** computation: `Fintype.card_perm` + `Fintype.card_fin`
   to establish $|S_3| = 6$.
2. A **group theory** lemma: `pow_card_eq_one` for the abstract result.

The connection between counting (factorial) and algebra (group order)
is exactly the bridge this world was designed to build.

## What comes next

The next worlds explore matrices as functions over finite types, and
further applications where permutations, finite types, and algebraic
structure interact.
"

/-- `pow_card_eq_one` states that in any finite group, every element
raised to the power of the group's cardinality equals the identity:

`x ^ Fintype.card G = 1`

This is a consequence of Lagrange's theorem.

**When to use**: To show that `σ ^ n = 1` where `n` is the order of
the group. First establish what `Fintype.card G` equals, then rewrite. -/
TheoremDoc pow_card_eq_one as "pow_card_eq_one" in "Equiv.Perm"

NewTheorem pow_card_eq_one
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
