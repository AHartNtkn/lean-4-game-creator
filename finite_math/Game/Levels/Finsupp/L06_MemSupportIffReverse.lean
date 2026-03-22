import Game.Metadata

World "Finsupp"
Level 6

Title "The Other Direction"

Introduction "
# Rewriting in a Hypothesis

In the last level you used `Finsupp.mem_support_iff` to convert a
goal about support membership into a goal about function values.
But `mem_support_iff` is an `↔` — it works in **both** directions.

The direction you haven't used yet is: given that `a` IS in the
support, conclude that `f a ≠ 0`. In practice this direction is
common — you often know something is in the support (for example
from `support_single_ne_zero`) and need to conclude the value
is nonzero.

To use the reverse direction, you rewrite **in the hypothesis**
rather than the goal. The syntax is:

```
rw [Finsupp.mem_support_iff] at h
```

This transforms `h : a ∈ f.support` into `h : f a ≠ 0`.

**Your task**: Given that `3` is in the support of `f`, prove
that `f 3 ≠ 0`.
"

/-- Support membership implies nonzero value. -/
Statement (f : ℕ →₀ ℕ) (h : 3 ∈ f.support) : f 3 ≠ 0 := by
  Hint "You have `h : 3 ∈ f.support` and need `f 3 ≠ 0`.
  Rewrite `mem_support_iff` in the hypothesis to convert it."
  Hint (hidden := true) "Try `rw [Finsupp.mem_support_iff] at h`.
  This changes `h` to `f 3 ≠ 0`."
  rw [Finsupp.mem_support_iff] at h
  Hint "Now `h` says exactly what the goal needs."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
The `rw [...] at h` syntax is a powerful tool: it rewrites inside
a hypothesis rather than the goal. Combined with `↔` lemmas like
`mem_support_iff`, it lets you freely convert between equivalent
forms on either side of the turnstile.

Both directions of `mem_support_iff` are now in your toolkit:
- **Goal**: `rw [Finsupp.mem_support_iff]` converts
  `a ∈ f.support` to `f a ≠ 0` (or vice versa)
- **Hypothesis**: `rw [Finsupp.mem_support_iff] at h` does the
  same transformation on `h`

This completes your understanding of the support-value bridge.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
