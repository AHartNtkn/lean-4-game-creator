import Game.Metadata

World "Finsupp"
Level 14

Title "Support of a Sum"

Introduction "
# Bounding the Support of a Sum

You know how to compute the support of individual singles. But what
about the support of `f + g`?

The key fact is that the support of a sum is **contained in** the
union of the individual supports:

```
Finsupp.support_add :
  (f + g).support ⊆ f.support ∪ g.support
```

This is containment (⊆), not equality — values can cancel! You
saw this in the last level: `single 4 5 + single 4 (-5) = 0` has
empty support, even though both summands have support containing `4`.

The containment direction is the useful one: if `x` is in the
support of a sum, then `x` must be in the support of at least one
summand.

Since `⊆` for `Finset` means `∀ x, x ∈ s → x ∈ t`, the lemma
`Finsupp.support_add` can be applied directly to a membership proof.

**Your task**: Given that `x` is in the support of `f + g`, prove
that `x` is in the union of the supports.
"

/-- The support of a sum is contained in the union of supports. -/
Statement (f g : ℕ →₀ ℕ) (x : ℕ) (hx : x ∈ (f + g).support) :
    x ∈ f.support ∪ g.support := by
  Hint "The lemma `Finsupp.support_add` says exactly this:
  `(f + g).support ⊆ f.support ∪ g.support`.
  Since `⊆` means every element of the left is in the right,
  you can apply `Finsupp.support_add` to `hx`."
  Hint (hidden := true) "Try `exact Finsupp.support_add hx`."
  exact Finsupp.support_add hx

Conclusion "
`Finsupp.support_add` bounds the support of a sum by the union of
the individual supports. This is useful in two ways:

1. **Upper bound**: If you know the supports of `f` and `g`, you
   know which points the sum *could* be nonzero at.
2. **Contrapositive**: If `x` is NOT in `f.support ∪ g.support`,
   then `x` is NOT in `(f + g).support` — so `(f + g) x = 0`.

The containment can be strict: `single a b + single a (-b)` has
empty support (you proved this in the cancellation level), while
both summands have support containing `a`. Cancellation explains
the gap between ⊆ and =.

Combined with `support_single_ne_zero`, you can now bound the
support of any sum of singles without evaluating pointwise.
"

/-- `Finsupp.support_add` bounds the support of a sum:

`Finsupp.support_add : (f + g).support ⊆ f.support ∪ g.support`

## Syntax
```
exact Finsupp.support_add hx   -- when hx : x ∈ (f + g).support
```

## When to use it
When you know something is in the support of a sum and need to
conclude it is in the support of one of the summands (via
union membership).

## Warning
This is ⊆, not =. Values can cancel, making the support of the
sum strictly smaller than the union of supports.
-/
TheoremDoc Finsupp.support_add as "Finsupp.support_add" in "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.support_add

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply Finsupp.single_add
