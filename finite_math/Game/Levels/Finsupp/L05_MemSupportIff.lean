import Game.Metadata

World "Finsupp"
Level 5

Title "Reading Support Membership"

Introduction "
# Support Membership Means Nonzero

You know what the support of a `single` looks like. For a general
finitely supported function `f`, the characterization is:

```
Finsupp.mem_support_iff : a ∈ f.support ↔ f a ≠ 0
```

This is the fundamental link between the support (a `Finset`) and
the function values. It says: `a` is in the support if and only if
`f` is nonzero at `a`.

Since this is an `↔`, you can use `rw` to convert between the
two forms.

**Your task**: Given that `f 5 ≠ 0`, prove that `5` is in the
support of `f`.
"

/-- Support membership is equivalent to nonzero value. -/
Statement (f : ℕ →₀ ℕ) (hf : f 5 ≠ 0) : 5 ∈ f.support := by
  Hint "The goal `5 ∈ f.support` is about support membership.
  Rewrite with `Finsupp.mem_support_iff` to convert it to the
  equivalent statement about values."
  Hint (hidden := true) "Try `rw [Finsupp.mem_support_iff]`. This
  changes the goal to `f 5 ≠ 0`."
  rw [Finsupp.mem_support_iff]
  Hint "The goal now matches hypothesis `hf` exactly."
  Hint (hidden := true) "Try `exact hf`."
  exact hf

Conclusion "
`Finsupp.mem_support_iff` is the bridge between two views of a
finitely supported function:

- **The support view**: `a ∈ f.support` (a finset membership question)
- **The value view**: `f a ≠ 0` (a question about the function output)

You can convert freely between them with `rw`. This is analogous
to `Finset.mem_filter` or `Finset.mem_image` — characterization
lemmas that translate between a structural description and a
logical description.

**Pattern**: `rw [Finsupp.mem_support_iff]` to switch from
support membership to nonzero-ness (or vice versa).
"

/-- `Finsupp.mem_support_iff` characterizes support membership:

`Finsupp.mem_support_iff : a ∈ f.support ↔ f a ≠ 0`

## Syntax
```
rw [Finsupp.mem_support_iff]       -- in the goal
rw [Finsupp.mem_support_iff] at h  -- in a hypothesis
```

## When to use it
When you need to connect support membership with function values.
Works in both directions since it's an `↔`.

## Example
If the goal is `5 ∈ f.support`, rewriting gives `f 5 ≠ 0`.
-/
TheoremDoc Finsupp.mem_support_iff as "Finsupp.mem_support_iff" in "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.mem_support_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
