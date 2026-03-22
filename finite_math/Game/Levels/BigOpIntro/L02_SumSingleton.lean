import Game.Metadata

World "BigOpIntro"
Level 2

Title "Sum Over a Singleton"

Introduction "
# Summing Over One Element

The next building block: what happens when you sum over a finset with
exactly one element?

$$\\sum_{x \\in \\{a\\}} f(x) = f(a)$$

Of course — summing a function over a single element just gives you
the function value at that element. In Lean:

```
Finset.sum_singleton : ∑ x ∈ {a}, f x = f a
```

**Your task**: You know that `s = {7}`. Prove that the sum of `f`
over `s` gives `f 7`.
"

/-- The sum of f over a singleton equals the function value. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ({7} : Finset ℕ)) :
    ∑ x ∈ s, f x = f 7 := by
  Hint "First substitute `s` with its value using `rw [hs]`."
  rw [hs]
  Hint "Now the goal is a sum over a singleton. Use
  `rw [Finset.sum_singleton]` to simplify."
  rw [Finset.sum_singleton]

Conclusion "
`Finset.sum_singleton` reduces a sum over a one-element finset to the
function value. Combined with `sum_empty`, you now have two base cases:

- Empty: `∑ x ∈ ∅, f x = 0`
- Singleton: `∑ x ∈ {a}, f x = f a`

In plain math: $\\sum_{{x \\in \\{a\\}}} f(x) = f(a)$. This is the
fact that makes singleton sums trivial — but it's essential for
unfolding larger sums down to concrete values.
"

/-- `Finset.sum_singleton` states that `∑ x ∈ {a}, f x = f a`.

## Syntax
```
rw [Finset.sum_singleton]
exact Finset.sum_singleton f a
```

## When to use it
When the goal involves a sum over a singleton finset `{a}`. After
rewriting, the sum disappears and you're left with `f a`.

## Example
```
-- Goal: ∑ x ∈ {5}, f x = f 5
rw [Finset.sum_singleton]
-- Goal: f 5 = f 5
```
-/
TheoremDoc Finset.sum_singleton as "Finset.sum_singleton" in "BigOp"

NewTheorem Finset.sum_singleton

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
