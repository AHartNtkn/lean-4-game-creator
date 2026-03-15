import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 1

Title "What is Finset.sum?"

Introduction
"
# Big sums over finite sets

Welcome to the **Finset.sum** world! In this world you will learn to
write and simplify big-sum expressions — the formal version of
$\\sum_{x \\in S} f(x)$.

## The idea

In ordinary mathematics you write
$$\\sum_{x \\in \\{1, 2, 3\\}} x^2 = 1 + 4 + 9 = 14.$$

In Lean 4 / mathlib the same idea is captured by `Finset.sum`:

```
Finset.sum s f
```

which means \"add up `f x` as `x` ranges over the elements of the
finset `s`.\" There is also a nice notation:

```
∑ x ∈ s, f x
```

## The type-class requirement

`Finset.sum` needs the result type to be an `AddCommMonoid` — a type
with `0`, `+`, and the laws that `+` is associative and commutative
and `0` is a neutral element. All of `Nat`, `Int`, `Rat`, and `Real`
satisfy this automatically.

## Your first task

Prove that `∑ x ∈ ({2} : Finset Nat), x = 2`.

This is just saying that the sum of a single element is that element
itself. The lemma `Finset.sum_singleton` handles it:

```
Finset.sum_singleton : ∀ {β : Type u_1} {α : Type u_2} [inst : AddCommMonoid β]
  (f : α → β) (a : α), ∑ x ∈ {a}, f x = f a
```

When the function is the identity (i.e., you sum the elements themselves),
`∑ x ∈ {2}, x` becomes just `2`.
"

/-- The sum of a single element is that element. -/
Statement : ∑ x ∈ ({2} : Finset Nat), x = 2 := by
  Hint "The sum over a singleton set equals the value at that element.
  Use `rw [Finset.sum_singleton]` to rewrite the sum."
  Hint (hidden := true) "Try `rw [Finset.sum_singleton]`."
  rw [Finset.sum_singleton]

Conclusion
"
You verified that `∑ x ∈ {2}, x = 2`. The key lemma is
`Finset.sum_singleton`:

```
∑ x ∈ {a}, f x = f a
```

The `∑ x ∈ s, f x` notation is just syntactic sugar for `Finset.sum s f`.
When the function is the identity, `∑ x ∈ s, x` adds up the elements
themselves.

## What comes next

We will now explore the basic API: what happens when the set is empty,
when it has one element, when you add an element, and when you take
a union.
"

/-- `Finset.sum_singleton` states that `∑ x ∈ {a}, f x = f a`.

The sum over a singleton finset equals the function applied to that
element. -/
TheoremDoc Finset.sum_singleton as "Finset.sum_singleton" in "Finset"

NewTheorem Finset.sum_singleton
DisabledTactic trivial decide native_decide simp aesop simp_all
