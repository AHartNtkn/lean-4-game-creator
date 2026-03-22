import Game.Metadata

World "BigOpIntro"
Level 13

Title "Rewriting the Factor"

Introduction "
# prod_congr: Changing What You Multiply

You learned `sum_congr` to rewrite the function inside a `∑`.
The multiplicative twin is `Finset.prod_congr`:

```
Finset.prod_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
  s₁.prod f = s₂.prod g
```

The pattern is identical to `sum_congr`:
1. `apply Finset.prod_congr rfl` — keep the finset, prove function equality
2. `intro x hx` — for each element in the finset...
3. Prove `f x = g x`

**Your task**: Given that `f x = x` for all `x ∈ s`, prove that
the product of `f` over `s` equals the product of `x` over `s`.
"

/-- `Finset.prod_congr` states that if `s₁ = s₂` and `∀ x ∈ s₂, f x = g x`,
then `s₁.prod f = s₂.prod g`.

## Syntax
```
apply Finset.prod_congr rfl   -- when the finsets are the same
intro x hx                    -- then prove f x = g x for each x ∈ s
```

## When to use it
When you need to rewrite the function inside a product. This is the
multiplicative analogue of `Finset.sum_congr`.
-/
TheoremDoc Finset.prod_congr as "Finset.prod_congr" in "BigOp"

/-- If f equals the identity on s, the products agree. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x = x) :
    ∏ x ∈ s, f x = ∏ x ∈ s, x := by
  Hint "The two products have the same finset but different functions.
  Use `apply Finset.prod_congr rfl` to reduce to proving they agree
  pointwise."
  apply Finset.prod_congr rfl
  Hint "Now prove `f x = x` for each `x ∈ s`. Start with `intro x hx`."
  intro x hx
  Hint "The hypothesis `hf` says exactly this. Use `exact hf x hx`."
  Hint (hidden := true) "Try `exact hf x hx`."
  exact hf x hx

Conclusion "
`prod_congr` is the multiplicative twin of `sum_congr`. The pattern
is identical:

1. `apply Finset.prod_congr rfl` — same finset, prove function equality
2. `intro x hx` — for each element...
3. Prove `f x = g x` using hypotheses or tactics

In the next level, you'll combine `prod_congr` with the peel pattern
to compute a concrete product from an abstract function.
"

/-- `ext` proves that two objects of the same type are equal by showing
their components are equal.

## Warning
In this level, `ext` is disabled because the goal is to learn
`prod_congr` — the big-operator-specific way to prove equality of
products by rewriting the factor.
-/
TacticDoc ext

/-- `congr` proves equality by reducing to equality of subexpressions.

## Warning
In this level, `congr` is disabled because the goal is to learn
`prod_congr` — the big-operator-specific way to prove equality of
products by rewriting the factor.
-/
TacticDoc congr

NewTheorem Finset.prod_congr

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext congr rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
