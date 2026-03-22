import Game.Metadata

World "BigOpIntro"
Level 8

Title "Rewriting the Summand"

Introduction "
# sum_congr: Changing What You Sum

Sometimes you want to rewrite the function inside a sum. For example,
if you know that `f(x) = g(x)` for every `x` in a finset, then:

$$\\sum_{x \\in s} f(x) = \\sum_{x \\in s} g(x)$$

The lemma for this is `Finset.sum_congr`:

```
Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
  s₁.sum f = s₂.sum g
```

When the finsets are the same (the common case), use `Finset.sum_congr rfl`
to supply the first argument:

```
apply Finset.sum_congr rfl
```

This leaves the goal: `∀ x ∈ s, f x = g x`. You then `intro x hx`
and prove the pointwise equality for each element.

**Your task**: Prove that `∑ x ∈ s, (0 + x) = ∑ x ∈ s, x`.
You might think the two sides are \"obviously equal,\" but Lean's kernel
doesn't simplify `0 + x` to `x` automatically (unlike `x + 0`, which
IS definitionally equal to `x`). You need `sum_congr` to rewrite
the summand pointwise, then `omega` to close each `0 + x = x` goal.
"

/-- Prepending zero inside a sum doesn't change the result. -/
Statement (s : Finset ℕ) :
    ∑ x ∈ s, (0 + x) = ∑ x ∈ s, x := by
  Hint "The two sums have the same finset but different functions:
  `fun x => 0 + x` vs `fun x => x`. Use `apply Finset.sum_congr rfl`
  to reduce to proving they agree pointwise."
  apply Finset.sum_congr rfl
  Hint "Now the goal asks you to prove `0 + x = x` for each `x` in
  the finset. Start with `intro x hx` to name the element and its
  membership proof."
  intro x hx
  Hint "The goal is `0 + x = x`. Close with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
`sum_congr` lets you rewrite the function inside a `∑` without
unfolding the entire sum. The pattern:

1. `apply Finset.sum_congr rfl` — keep the finset, prove function equality
2. `intro x hx` — for each element `x` in the finset...
3. Prove `f x = g x` using whatever tools work (`omega`, `rw`, etc.)

The `rfl` argument says the finsets are the same. You could also use
`sum_congr` with different finsets if you have a proof they're equal.

**Why didn't `rfl` work here?** In Lean, `x + 0 = x` is *definitionally*
true (it's the base case of `Nat.add`), but `0 + x = x` is NOT
definitional — it requires induction on `x`. So `rfl` would close
`∑ x ∈ s, (x + 0) = ∑ x ∈ s, x` but not this version. This is a
subtlety of how `Nat.add` is defined by recursion on its second argument.

In plain math: if $f(x) = g(x)$ for all $x \\in s$, then
$\\sum_{{x \\in s}} f(x) = \\sum_{{x \\in s}} g(x)$.
"

/-- `Finset.sum_congr` states that if `s₁ = s₂` and `∀ x ∈ s₂, f x = g x`,
then `s₁.sum f = s₂.sum g`.

## Syntax
```
apply Finset.sum_congr rfl   -- when the finsets are the same
intro x hx                    -- then prove f x = g x for each x ∈ s
```

## When to use it
When you need to rewrite the function inside a sum. This is the
big-operator analogue of rewriting under a binder.

## Example
```
-- Goal: ∑ x ∈ s, (0 + x) = ∑ x ∈ s, x
apply Finset.sum_congr rfl
intro x hx
omega
```
-/
TheoremDoc Finset.sum_congr as "Finset.sum_congr" in "BigOp"

/-- `ext` proves that two objects of the same type are equal by showing
their components are equal.

## Warning
In this level, `ext` is disabled because the goal is to learn
`sum_congr` — the big-operator-specific way to prove equality of
sums by rewriting the summand.
-/
TacticDoc ext

/-- `congr` proves equality by reducing to equality of subexpressions.

## Warning
In this level, `congr` is disabled because the goal is to learn
`sum_congr` — the big-operator-specific way to prove equality of
sums by rewriting the summand.
-/
TacticDoc congr

NewTheorem Finset.sum_congr

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext congr
DisabledTheorem Finset.sum_pair Finset.prod_pair
