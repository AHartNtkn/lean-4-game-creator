import Game.Metadata

World "FinsetInduction"
Level 1

Title "First Contact with Finset Induction"

Introduction "
# Induction on Finsets

You already know how to prove things about natural numbers by induction:
show the base case ($n = 0$), then show the inductive step
($n \\to n + 1$). **Finset induction** works the same way, but for
finite sets:

- **Base case**: prove the statement for the empty set $\\emptyset$
- **Inductive step**: given that the statement holds for some finset $s$,
  and given a fresh element $a \\notin s$, prove it for
  $\\text{insert } a\\ s$

In Lean, you invoke this with:
```
induction s using Finset.induction_on with
| empty => ...
| @insert a s ha ih => ...
```

The `@` in `@insert` tells Lean to expose all arguments (including
implicit ones like the non-membership proof `ha`) as pattern variables.
Without `@`, you wouldn't be able to name `ha` directly.

In the `insert` branch, you get:
- `a : \\alpha` — the new element being inserted
- `s : Finset \\alpha` — the smaller finset
- `ha : a \\notin s` — proof that `a` is not already in `s`
- `ih` — the induction hypothesis: the statement holds for `s`

**Your task**: Prove that the sum of the constant function $0$ over any
finset is $0$. This is mathematically obvious, but the point is to
see the induction structure.
"

/-- The sum of 0 over any finset is 0, proved by finset induction. -/
Statement (s : Finset ℕ) : ∑ _x ∈ s, (0 : ℕ) = 0 := by
  Hint "Start by invoking finset induction:
  `induction s using Finset.induction_on with`
  `| empty => ...`
  `| @insert a s ha ih => ...`

  This creates two goals: the base case (empty set) and the
  inductive step (insert)."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty =>`
  `  sorry`
  `| @insert a s ha ih =>`
  `  sorry`

  Then replace each `sorry` with the actual proof."
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: The goal is `∑ x ∈ ∅, 0 = 0`.
    You know `Finset.sum_empty` from BigOpIntro.
    Use `rw [Finset.sum_empty]` to rewrite the empty sum to `0`."
    Hint (hidden := true) "Try `rw [Finset.sum_empty]`."
    rw [Finset.sum_empty]
  | @insert a s ha ih =>
    Hint "**Inductive step**: The goal is
    `∑ x ∈ insert a s, 0 = 0`.

    You have:
    - `ha : a ∉ s`
    - `ih : ∑ x ∈ s, 0 = 0`

    First, peel off the inserted element with `Finset.sum_insert ha`.
    This gives `0 + ∑ x ∈ s, 0 = 0`."
    Hint (hidden := true) "Try `rw [Finset.sum_insert ha]`."
    rw [Finset.sum_insert ha]
    Hint "Now the goal is `0 + ∑ x ∈ s, 0 = 0`.
    Apply the induction hypothesis `ih` to replace the remaining
    sum with `0`. The resulting `0 + 0 = 0` closes automatically."
    Hint (hidden := true) "Try `rw [ih]`."
    rw [ih]

Conclusion "
You just completed your first finset induction proof! The pattern was:

1. `induction s using Finset.induction_on` to set up two goals
2. **Base**: `sum_empty` closes the empty-set case
3. **Step**: `sum_insert ha` peels off the new element, then the
   induction hypothesis `ih` handles the rest. The remaining
   arithmetic (`0 + 0 = 0`) closes by computation.

This is the fundamental pattern for all finset induction proofs.
The algebra in the inductive step will get more interesting in
the coming levels, but the skeleton stays the same.

**Why does finset induction work?** Recall from the Abstraction
Ladder that a `Finset` is built on a `Multiset` (which is built on
a `List`). Finset induction is ultimately structural induction on
the underlying list, made order-independent by the multiset quotient.
The `a \\notin s` condition exists because inserting a duplicate would
collapse in the quotient — it's a no-duplicate constraint. So the
insert step really is adding a genuinely new element, just like
`n \\to n + 1` adds a genuinely new natural number.
"

/-- `Finset.induction_on` is the induction principle for finsets.
To prove a property holds for all finsets, prove it for `\\emptyset`
(base case) and prove that if it holds for `s`, it holds for
`insert a s` when `a \\notin s` (inductive step).

## Syntax
```
induction s using Finset.induction_on with
| empty => base_proof
| @insert a s ha ih => step_proof
```

## Variables in the insert branch
- `a` — the new element
- `s` — the smaller finset
- `ha : a \\notin s` — non-membership proof
- `ih` — induction hypothesis (the statement for `s`)

## When to use it
When you need to prove a property of an arbitrary `Finset` and
can handle the empty and insert cases separately.
-/
TheoremDoc Finset.induction_on as "Finset.induction_on" in "Finset"

/-- `induction` performs structural induction on an inductive type.

## Syntax — natural number induction
```
induction n with
| zero => base_proof
| succ n ih => step_proof
```

## Syntax — finset induction
```
induction s using Finset.induction_on with
| empty => base_proof
| @insert a s ha ih => step_proof
```

## When to use it
When you need to prove a property for all values of an inductive
type by handling each constructor case.

## Key detail
The `using` clause selects which induction principle to use.
Without `using`, Lean picks the default recursor for the type.
-/
TacticDoc induction

TheoremTab "BigOp"
NewTactic induction
NewTheorem Finset.induction_on

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_const_zero Finset.sum_eq_zero Finset.sum_range_sub Finset.eq_sum_range_sub
