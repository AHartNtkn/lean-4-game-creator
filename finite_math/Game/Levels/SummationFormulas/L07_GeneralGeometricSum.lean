import Game.Metadata

World "SummationFormulas"
Level 7

Title "The General Geometric Sum"

Introduction "
# The Geometric Series for Any Base

In Level 5 you proved the geometric sum for base $2$:
$$\\sum_{i=0}^{n-1} 2^i + 1 = 2^n$$

In Level 6 you proved it for base $3$:
$$2 \\cdot \\sum_{i=0}^{n-1} 3^i + 1 = 3^n$$

Both conclusions noted that the proof works for any base. Now you
will prove the **general geometric sum formula**:

$$q \\cdot \\sum_{i=0}^{n-1} (q+1)^i + 1 = (q+1)^n$$

This is the formula $(q-1) \\cdot \\sum r^i = r^n - 1$ with $r = q+1$,
rewritten to avoid natural number subtraction (since $r - 1$ on
$\\mathbb{N}$ is truncated). With $r = q + 1$, the factor $r - 1 = q$
is just a natural number — no subtraction needed.

**Check the special cases**:
- $q = 1$ (base 2): $1 \\cdot \\sum 2^i + 1 = 2^n$, matching Level 5
- $q = 2$ (base 3): $2 \\cdot \\sum 3^i + 1 = 3^n$, matching Level 6

**The key insight**: The proof is structurally identical to Levels 5
and 6. After peeling and distributing, the IH's pattern
$q \\cdot \\sum + 1$ appears (after rearranging addition), and then
the closing step uses `ring` instead of `have` + `ring` + `omega`.
"

/-- The general geometric sum: q times the sum of (q+1)^i, plus 1, equals (q+1)^n. -/
Statement (q n : ℕ) : q * (∑ i ∈ Finset.range n, (q + 1) ^ i) + 1 = (q + 1) ^ n := by
  Hint "Induct on `n` — exactly the same skeleton as Levels 5 and 6."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: `range 0` is empty, so the sum is $0$.
    The goal becomes $q \\cdot 0 + 1 = (q+1)^0 = 1$."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel with `sum_range_succ`, then
    distribute the $q$ with `mul_add` to separate the sum (which
    the IH knows about) from the new $(q+1)^n$ term."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, mul_add]`."
    rw [Finset.sum_range_succ, mul_add]
    Hint "Now rearrange so the IH's pattern `q * ∑ + 1` appears.
    After distributing, the goal has the shape:
    `q * ∑ + q * (q+1)^n + 1 = (q+1)^(n+1)`.

    You need `q * ∑ + 1` (the IH's left side) to be visible.
    Commute the addition with `add_right_comm` to get
    `q * ∑ + 1 + q * (q+1)^n`, then `rw [ih]` fires."
    Hint (hidden := true) "Try `rw [add_right_comm, ih]` then `ring`."
    rw [add_right_comm, ih]
    Hint "After substituting the IH:
    `(q+1)^n + q * (q+1)^n = (q+1)^(n+1)`.
    This factors as $(1 + q) \\cdot (q+1)^n = (q+1)^(n+1)$. `ring` closes it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved the general geometric sum formula:
$$q \\cdot \\sum_{i=0}^{n-1} (q+1)^i + 1 = (q+1)^n$$

**What generalization bought you**: Levels 5 and 6 proved the same
identity for specific values of $q$. The general proof is *structurally
identical* — the only difference is using `ring` (which handles
arbitrary polynomial identities) instead of `have + ring + omega`
(which was needed when the exponent base was a specific number).

**Avoiding natural number subtraction**: The standard formula is
$(q-1) \\cdot \\sum q^i = q^n - 1$, but both sides involve subtraction
on $\\mathbb{N}$, which is truncated. By writing $q+1$ as the base
instead of $q$, we replaced $q - 1$ with a plain natural number $q$
and eliminated the right-hand subtraction too. This substitution
technique — replacing $q$ with $q + 1$ to avoid subtraction — is a
standard formalization trick for natural number arithmetic.

**The rearrangement trick**: In Levels 5 and 6, `omega` handled the
final arithmetic because the exponent bases (2 and 3) were specific
numbers. With a variable base $q+1$, `omega` can't help (it only
handles linear arithmetic). Instead, you used `add_right_comm` to
rearrange $q \\cdot \\sum + q \\cdot (q+1)^n + 1$ into
$(q \\cdot \\sum + 1) + q \\cdot (q+1)^n$, making the IH's
pattern visible. Then `ring` closed the factoring step.

**`add_right_comm` as a general tool**: Whenever the IH's pattern
$A + B$ appears in the goal as $A + C + B$ (with an extra term $C$
in the middle), `add_right_comm` reorders to $A + B + C$, making
`rw [ih]` fire. This pattern-alignment move comes up whenever you
need to rearrange addition to expose a rewrite target.
"

/-- `add_right_comm` states that `a + b + c = a + c + b`.

Commutes the second and third terms of a three-way sum.

## Syntax
```
rw [add_right_comm]
```

## When to use it
When you need to rearrange the order of addition to match a
pattern for rewriting. For example, if the IH matches `a + 1`
but the goal has `a + b + 1`, use `add_right_comm` to get
`a + 1 + b`, then `rw [ih]` fires.
-/
TheoremDoc add_right_comm as "add_right_comm" in "Algebra"

NewTheorem add_right_comm

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.geom_sum_eq Finset.geom_series_def Finset.pow_eq_prod_const Finset.prod_const
