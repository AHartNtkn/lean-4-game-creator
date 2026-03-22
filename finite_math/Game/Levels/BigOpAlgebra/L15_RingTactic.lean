import Game.Metadata

World "BigOpAlgebra"
Level 15

Title "Algebraic Simplification with ring"

Introduction "
# ring: Closing Algebraic Goals

After transforming sums with big-operator lemmas, you often end up
with a goal that is pure algebra — rearranging additions and
multiplications. The `ring` tactic closes such goals automatically.

**What `ring` can do**:
- `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2` ✓
- `a * (b + c) = a * b + a * c` ✓
- Commutativity, associativity, distributivity ✓

**What `ring` cannot do**:
- Anything involving hypotheses (it only looks at the goal)
- Anything involving `∑`, `∏`, membership, or non-ring operations

So `ring` complements the big-operator lemmas: the lemmas reduce
sum expressions to algebraic form, and `ring` closes the algebra.

There is also `ring_nf`, which normalizes ring expressions without
necessarily closing the goal. Use `ring_nf` when `ring` alone
doesn't close the goal but you want to simplify the algebra.

**`ring` vs `omega`**: You already know `omega` from earlier worlds.
The distinction: `omega` handles **linear** arithmetic over `ℕ`
and `ℤ` — it can use hypotheses and solve `a + b = b + a` or
`n < n + 1`, but it cannot handle multiplication of variables
or exponents. `ring` handles **polynomial** identities over any
commutative (semi)ring — it can expand `(a + b)^2` and collect
like terms, but it ignores all hypotheses. Use `omega` for linear
goals with hypotheses; use `ring` for algebraic identities.

**The two-phase pattern**:
1. Use big-operator lemmas to transform sums
2. Use `ring` to close the resulting algebra

**Your task**: Prove the square-of-sum identity for big operators.
First use `sum_add_distrib` to eliminate the `∑(f + g)` expression,
then close with `ring`. The resulting identity —
`(a + b)² = a² + 2ab + b²` — is the kind of algebraic
rearrangement `ring` excels at.
"

/-- The two-phase pattern: big-operator rewrite, then ring. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ) :
    (∑ x ∈ s, (f x + g x)) ^ 2 =
    (∑ x ∈ s, f x) ^ 2 + 2 * (∑ x ∈ s, f x) * (∑ x ∈ s, g x) +
    (∑ x ∈ s, g x) ^ 2 := by
  Hint "`ring` can rearrange algebra, but not big-operator
  expressions. First use `rw [Finset.sum_add_distrib]` to
  eliminate the big operator, then `ring` to close."
  rw [Finset.sum_add_distrib]
  Hint "The goal is now `(∑f + ∑g)² = (∑f)² + 2·(∑f)·(∑g) + (∑g)²`.
  This is pure algebra — `ring` sees `∑f` and `∑g` as opaque
  values and recognizes the square-of-sum identity."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
`ring` is your algebraic closer. The typical workflow is:

1. **Phase 1**: Use `sum_add_distrib`, `sum_const`, `sum_union`,
   etc. to transform sum structure into algebraic combinations
2. **Phase 2**: Use `ring` to close the algebra

Notice that before the rewrite, `ring` can't help — it doesn't
understand `∑(f + g)`. After `sum_add_distrib` converts the sum
into `∑f + ∑g`, `ring` treats these as opaque variables and
handles the algebra.

**Warning**: `ring` ignores hypotheses entirely. If your goal
needs a hypothesis to be true, you must `rw` that hypothesis
first, then use `ring` to close what remains.

`ring_nf` is the normalization variant — it simplifies without
necessarily closing the goal. Use it when `ring` fails but you
want Lean to clean up the algebra.
"

/-- `ring` closes goals that are equalities in commutative (semi)rings
by normalizing both sides.

## Syntax
```
ring
```

## When to use it
When the goal is a pure algebraic equation involving `+`, `*`, `^`,
`0`, `1`, and numeric literals. `ring` treats unknown terms (like
`∑ f`) as opaque variables.

## What ring can do
- Commutativity: `a + b = b + a`
- Associativity: `(a + b) + c = a + (b + c)`
- Distributivity: `a * (b + c) = a * b + a * c`
- Powers: `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`
- Collect like terms: `a + a = 2 * a`

## What ring cannot do
- Use hypotheses (it only looks at the goal)
- Simplify `∑`, `∏`, or membership expressions
- Handle subtraction on ℕ (use `omega` for that)

## Warning
`ring` ignores all hypotheses. If the goal requires a hypothesis,
`rw` it into the goal first, then use `ring` to close the algebra.
-/
TacticDoc ring

/-- `ring_nf` normalizes ring expressions without necessarily closing
the goal. Use it when `ring` alone doesn't close the goal but you
want to simplify the algebra.

## Syntax
```
ring_nf
ring_nf at h    -- normalize a hypothesis
```

## When to use it
When `ring` fails (perhaps because the goal isn't purely algebraic)
but you want Lean to simplify the ring parts as much as possible.
-/
TacticDoc ring_nf

NewTactic ring ring_nf

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
