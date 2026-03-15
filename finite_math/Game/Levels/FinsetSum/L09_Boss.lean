import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 9

Title "Boss: Multi-step sum simplification"

Introduction
"
# Boss: Simplify a big-sum expression

Time to integrate everything. You will prove a concrete sum identity
by combining `sum_insert`, `sum_singleton`, `sum_union`, and arithmetic.

## The statement

Prove that the sum of `2 * x` over the union of `{1, 2}` and `{3}`
equals `12`.

## Strategy

1. Use `sum_union` to split the sum over the disjoint union.
2. Use `sum_insert` on `insert 1 (singleton 2)` to peel off `1`.
3. Use `sum_singleton` twice for the remaining singletons.
4. Evaluate the arithmetic: `(2 + 4) + 6 = 12`.

You will need to supply disjointness and non-membership proofs along
the way.
"

/-- Evaluate a sum over a union. -/
Statement : ∑ x ∈ ({1, 2} : Finset Nat) ∪ {3}, (2 * x) = 12 := by
  Hint "Start by splitting the sum over the union using `Finset.sum_union`.
  You need a proof of disjointness.

  Try:
  `have hd : Disjoint ... ... := by norm_num [Finset.disjoint_left]`
  then `rw [Finset.sum_union hd]`."
  have hd : Disjoint ({1, 2} : Finset Nat) ({3} : Finset Nat) := by
    norm_num [Finset.disjoint_left]
  rw [Finset.sum_union hd]
  Hint "Now decompose the sum over `insert 1 (singleton 2)` using `sum_insert`.
  You need a proof that `1` is not in the singleton.

  Try:
  `have h1 : (1 : Nat) ∉ ... := by norm_num`
  then `rw [Finset.sum_insert h1]`."
  have h1 : (1 : Nat) ∉ ({2} : Finset Nat) := by norm_num
  rw [Finset.sum_insert h1]
  Hint "Now apply `sum_singleton` to the remaining singletons and
  finish with arithmetic."
  Hint (hidden := true) "Use `rw [Finset.sum_singleton, Finset.sum_singleton]`."
  rw [Finset.sum_singleton]
  Hint "Apply one more `sum_singleton` and the arithmetic will resolve."
  rw [Finset.sum_singleton]

Conclusion
"
Congratulations on completing the Finset.sum world!

You proved a concrete sum identity by combining:
1. `sum_union` to split the sum over a disjoint union
2. `sum_insert` to peel off elements from an `insert`-constructed finset
3. `sum_singleton` to reduce a singleton sum to a function application
4. Arithmetic to evaluate the result

## What you learned in this world

- L01: Big-sum notation and `sum_singleton`
- L02: Empty sum is zero (`sum_empty`)
- L03: Practicing `sum_singleton`
- L04: Decomposing via `cons` (`sum_cons`)
- L05: Decomposing via `insert` (`sum_insert`)
- L06: Why `AddCommMonoid` is needed (commutativity)
- L07: Step-by-step concrete computation
- L08: Splitting over disjoint unions (`sum_union`)
- L09: Integration (boss)

## Transfer moment

In ordinary mathematics, evaluating a finite sum is straightforward:
you just add up the terms. In Lean, the same process is made explicit
through decomposition lemmas. Each `sum_insert` or `sum_singleton`
corresponds to one step of writing out the sum.

The `AddCommMonoid` requirement makes precise a fact that is usually
taken for granted: finite sums over unordered collections are only
well-defined when addition is commutative.

**In plain language**: To compute a finite sum, repeatedly peel off
elements using `sum_insert` or `sum_cons`, handle the last element
with `sum_singleton`, and evaluate the arithmetic. For unions,
`sum_union` splits the sum when the parts are disjoint.

## What comes next

The next world introduces **induction on range sums**: proving identities
like `∑ i ∈ range n, f i = ...` by induction on `n`, using
`sum_range_succ` to peel off the last term.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
