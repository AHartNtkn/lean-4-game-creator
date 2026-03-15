import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 6

Title "The AddCommMonoid requirement"

Introduction
"
# Why does `Finset.sum` need `AddCommMonoid`?

Look at the type of `Finset.sum`:

```
Finset.sum (s : Finset α) (f : α → β) : β
```

where `β` must be an `AddCommMonoid`. Why?

## The reason: order independence

A `Finset` has **no order**. When you write `∑ x ∈ {1, 2, 3}, f x`,
there is no canonical order in which to add the terms. The sum could
be computed as:
- `f 1 + f 2 + f 3`, or
- `f 2 + f 1 + f 3`, or
- `f 3 + f 1 + f 2`, etc.

For the sum to be well-defined, all these orders must give the same
result. This is exactly what **commutativity** (`a + b = b + a`) and
**associativity** (`(a + b) + c = a + (b + c)`) guarantee.

The **monoid** part provides a `0` element, which is needed for the
empty sum.

Together, `AddCommMonoid` ensures:
1. `0` exists (for `sum_empty`)
2. `+` is associative (for regrouping)
3. `+` is commutative (for reordering)

## Your task

To make this concrete, prove that the order of summation does not
matter. Given `s : Finset Nat`, an element `a` with `ha : a ∉ s`,
and a function `f`, show:

```
f a + ∑ x ∈ s, f x = ∑ x ∈ s, f x + f a
```

This is commutativity of addition applied to a sum expression.
You can close this with `omega` (which knows commutativity for `Nat`).
"

/-- Reordering a sum: `f a` can go on either side. -/
Statement (s : Finset Nat) (a : Nat) (f : Nat → Nat) :
    f a + ∑ x ∈ s, f x = ∑ x ∈ s, f x + f a := by
  Hint "The goal is `f a + ∑ x ∈ s, f x = ∑ x ∈ s, f x + f a`.
  This is just commutativity of addition: `a + b = b + a`.

  Use `omega` to close this — it understands that natural number
  addition is commutative."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion
"
You proved that the summand `f a` can be placed on either side of the sum.
This used commutativity of addition (`a + b = b + a`).

## The key lesson

Without commutativity, we could not conclude `f a + S = S + f a`
(where `S = ∑ x ∈ s, f x`). This is exactly why `Finset.sum`
requires `AddCommMonoid`:

- **Associativity** lets us regroup: `(a + b) + c = a + (b + c)`
- **Commutativity** lets us reorder: `a + b = b + a`
- **Identity** gives us the empty sum: `∑ x ∈ ∅, f x = 0`

For natural numbers, integers, rationals, and reals, all three hold
automatically. But if you tried to define a \"sum\" over a finset
in a non-commutative setting, different orderings of the elements
would give different results, and the operation would not be well-defined.

## Comparison with lists

Recall that a `List` *does* have an order, so `List.sum` only needs
`AddMonoid` (not `AddCommMonoid`). The commutativity requirement is
specific to `Finset` and `Multiset`, which are unordered.

**In plain language**: \"Finite sums over unordered collections require
commutativity because the collection has no canonical order. The
`AddCommMonoid` type class guarantees that the sum is independent of
the traversal order.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
