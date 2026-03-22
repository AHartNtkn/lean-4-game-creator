import Game.Metadata

World "BigOpIntro"
Level 6

Title "The Empty Product"

Introduction "
# Big Products: ∏

Everything you've learned about `∑` has a multiplicative twin: `∏`.

The notation `∏ x ∈ s, f x` means: *multiply f(x) over all elements
x in the finset s*. In ordinary math:

$$\\prod_{x \\in s} f(x)$$

The key lemmas are exact multiplicative analogues:

| Additive (∑) | Multiplicative (∏) |
|---|---|
| `sum_empty` : empty sum = 0 | `prod_empty` : empty product = 1 |
| `sum_singleton` : singleton sum = f a | `prod_singleton` : singleton product = f a |
| `sum_insert` : ... = f a + ∑ ... | `prod_insert` : ... = f a * ∏ ... |

Notice: the empty **product** is `1` (the multiplicative identity),
just as the empty **sum** is `0` (the additive identity).

**Your task**: You know `s` is empty. Prove that the product of any
function over `s` is 1.
"

/-- The product of any function over the empty finset is 1. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ∅) :
    ∏ x ∈ s, f x = 1 := by
  Hint "First substitute `s` using `rw [hs]`, then apply the
  product-empty lemma."
  rw [hs]
  Hint (hidden := true) "Try `exact Finset.prod_empty`."
  exact Finset.prod_empty

Conclusion "
`Finset.prod_empty` is the multiplicative base case: the empty
product equals `1`.

**Why 1?** The product of no factors is the multiplicative identity,
just as the sum of no terms is the additive identity (0).

This parallels a familiar convention: $0! = 1$ is the empty product
of positive integers.

| | Sum (∑) | Product (∏) |
|---|---|---|
| Empty | 0 | 1 |
| Singleton | f a | f a |
| Insert | f a + ∑ ... | f a * ∏ ... |
"

/-- `Finset.prod s f` (written `∏ x ∈ s, f x`) computes the product of
`f x` over all elements `x` in the finset `s`.

## Notation
`∏ x ∈ s, f x` — product of `f` over finset `s`.

## Type
`Finset.prod : Finset ι → (ι → M) → M` where `M` has `CommMonoid`.

## Key lemmas
- `Finset.prod_empty : ∏ x ∈ ∅, f x = 1`
- `Finset.prod_singleton : ∏ x ∈ {a}, f x = f a`
- `Finset.prod_insert : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x`
-/
DefinitionDoc Finset.prod as "Finset.prod"

/-- `Finset.prod_empty` states that `∏ x ∈ ∅, f x = 1`.

The empty product is the multiplicative identity `1`,
just as the empty sum is the additive identity `0`.

## Syntax
```
exact Finset.prod_empty
rw [Finset.prod_empty]
```
-/
TheoremDoc Finset.prod_empty as "Finset.prod_empty" in "BigOp"

/-- `Finset.prod_singleton` states that `∏ x ∈ {a}, f x = f a`.

## Syntax
```
rw [Finset.prod_singleton]
```
-/
TheoremDoc Finset.prod_singleton as "Finset.prod_singleton" in "BigOp"

/-- `Finset.prod_insert` states that if `a ∉ s`, then
`∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x`.

## Syntax
```
rw [Finset.prod_insert h]  -- where h : a ∉ s
```

The proof `h : a ∉ s` is required to avoid double-counting.
-/
TheoremDoc Finset.prod_insert as "Finset.prod_insert" in "BigOp"

NewDefinition Finset.prod
NewTheorem Finset.prod_empty

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
