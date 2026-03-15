import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 3

Title "Finsupp.support: the finite set of nonzero points"

Introduction
"
# The Support of a `Finsupp`

Every finitely supported function `f : α →₀ M` has a **support**: a
`Finset α` containing exactly the points where `f` is nonzero.

```
Finsupp.support : (α →₀ M) → Finset α
```

## Support membership

The key characterization is:
```
Finsupp.mem_support_iff : a ∈ f.support ↔ f a ≠ 0
```

An element `a` is in the support of `f` if and only if `f a ≠ 0`.

## Support of `single`

For `Finsupp.single a b` with `b ≠ 0`, the support is exactly `{a}`:
```
Finsupp.support_single_ne_zero :
  b ≠ 0 → (Finsupp.single a b).support = {a}
```

Note that `Finsupp.support_single_ne_zero` takes the *point* `a` as its
first explicit argument and a proof of `b ≠ 0` as its second.

## Your task

Prove that the support of `Finsupp.single 3 5` is `{3}`.

Since `5 ≠ 0`, you can use `Finsupp.support_single_ne_zero` directly.
Supply the proof `(by omega)` for `5 ≠ 0`.
"

/-- The support of `Finsupp.single 3 5` is `{3}`. -/
Statement : (Finsupp.single 3 (5 : ℕ)).support = {3} := by
  Hint "Use `exact Finsupp.support_single_ne_zero 3 (by omega)`.

  The first argument `3` is the point, and `by omega` proves `5 ≠ 0`."
  Hint (hidden := true) "Try `exact Finsupp.support_single_ne_zero 3 (by omega)`."
  exact Finsupp.support_single_ne_zero 3 (by omega)

Conclusion
"
You computed the support of a `Finsupp.single`.

## The support concept

The support is a `Finset` — not a `Set` — which means it carries
concrete, computable data about which points are nonzero. This is the
key advantage of `Finsupp` over arbitrary functions: the finiteness of
the nonzero set is baked into the type.

## Two views of support

| Lemma | What it says |
|-------|-------------|
| `mem_support_iff` | `a ∈ f.support ↔ f a ≠ 0` |
| `support_single_ne_zero` | `b ≠ 0 → (single a b).support = {a}` |

The first is the general characterization. The second is the computation
rule for the `single` constructor.

**In plain language**: \"The support of a finitely supported function is
the finite set of points where it is nonzero. For `single a b`, that
set is just `{a}` (provided `b ≠ 0`).\"
"

/-- `Finsupp.support f` is the `Finset` of points where `f` is nonzero.

**Type**: `Finsupp.support : (α →₀ M) → Finset α`

**Characterization**: `a ∈ f.support ↔ f a ≠ 0`
(see `Finsupp.mem_support_iff`). -/
DefinitionDoc Finsupp.support as "Finsupp.support"

/-- `Finsupp.support_single_ne_zero a h` proves that the support of
`Finsupp.single a b` is `{a}`, given `h : b ≠ 0`.

```
Finsupp.support_single_ne_zero (a : α) (h : b ≠ 0) :
  (Finsupp.single a b).support = {a}
```

**When to use**: To compute the support of a `Finsupp.single`
when the value is nonzero. -/
TheoremDoc Finsupp.support_single_ne_zero as "Finsupp.support_single_ne_zero" in "Finsupp"

/-- `Finsupp.mem_support_iff` characterizes membership in the support:

```
a ∈ f.support ↔ f a ≠ 0
```

**When to use**: To convert between \"a is in the support\" and
\"f a is nonzero,\" or vice versa. -/
TheoremDoc Finsupp.mem_support_iff as "Finsupp.mem_support_iff" in "Finsupp"

NewDefinition Finsupp.support
NewTheorem Finsupp.support_single_ne_zero Finsupp.mem_support_iff
TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
