import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 1

Title "What is Finsupp?"

Introduction
"
# Finitely Supported Functions

Welcome to the world of **finitely supported functions**!

## The idea

In many areas of mathematics, you work with functions that are nonzero
at only finitely many points. Examples include:

- **Polynomials**: A polynomial $p(x) = a_0 + a_1 x + \\cdots + a_n x^n$
  is a function from $\\mathbb{N}$ to a ring, where $a_i \\neq 0$ for only
  finitely many $i$.
- **Free abelian groups**: An element of the free abelian group on a set
  $S$ is a function $S \\to \\mathbb{Z}$ that is nonzero at finitely many
  points.
- **Formal sums**: A finite formal sum $\\sum_{i \\in I} a_i \\cdot e_i$ is
  a function $I \\to R$ with finite support.

## `Finsupp` in Mathlib

Mathlib captures this idea with the type `α →₀ M`, pronounced
\"finitely supported functions from `α` to `M`.\" Here `M` must have
a zero element (an instance of `Zero M`), and `α →₀ M` consists of
functions `f : α → M` such that `f a ≠ 0` for only finitely many `a`.

The notation `α →₀ M` is syntactic sugar for `Finsupp α M`.

## Evaluating a `Finsupp`

A `Finsupp` can be applied to any element of `α` — it is a *total*
function, not a partial function. If `f : α →₀ M`, then `f a : M`
is defined for every `a : α`.

The simplest `Finsupp` is `Finsupp.single a b`, which sends `a` to `b`
and everything else to `0`. The evaluation rule is:

```
Finsupp.single_apply : (Finsupp.single a b) a' = if a = a' then b else 0
```

## Your task

Evaluate `Finsupp.single 3 5` at the point `3`. The result should be `5`.

Use `rw [Finsupp.single_apply]` to unfold the definition, then
`rw [if_pos rfl]` to resolve the conditional (since `3 = 3` is true).
"

/-- Evaluating `Finsupp.single 3 5` at `3` gives `5`. -/
Statement : (Finsupp.single 3 (5 : ℕ)) 3 = 5 := by
  Hint "Use `rw [Finsupp.single_apply]` to unfold the definition of
  `Finsupp.single`. This will produce an `if`-`then`-`else` expression."
  rw [Finsupp.single_apply]
  Hint "The goal is now `(if 3 = 3 then 5 else 0) = 5`.
  Since `3 = 3` is true, use `rw [if_pos rfl]` to simplify the conditional."
  Hint (hidden := true) "Use `rw [if_pos rfl]`."
  rw [if_pos rfl]

Conclusion
"
You evaluated a finitely supported function at a point in its support.

## The evaluation pattern

The key lemma `Finsupp.single_apply` reduces evaluation of
`Finsupp.single a b` to a conditional:

```
(Finsupp.single a b) a' = if a = a' then b else 0
```

When `a = a'`, the result is `b`. When `a ≠ a'`, the result is `0`.

After rewriting with `single_apply`, you resolve the conditional using
`if_pos` (when the condition is true) or `if_neg` (when it is false).

**In plain language**: \"A finitely supported function assigns a value
to one point and zero everywhere else — and `single_apply` is the
formal way to read off that value.\"
"

/-- `Finsupp α M` (notation: `α →₀ M`) is the type of functions from `α`
to `M` that are nonzero at only finitely many points.

A `Finsupp` can be applied to any `a : α` to get `f a : M`. It is a
total function, not a partial function.

**Key construction**: `Finsupp.single a b` sends `a` to `b` and
everything else to `0`. -/
DefinitionDoc Finsupp as "Finsupp"

/-- `Finsupp.single a b` constructs a finitely supported function that
sends `a` to `b` and everything else to `0`.

**Type**: `Finsupp.single (a : α) (b : M) : α →₀ M`

**Evaluation**: `(Finsupp.single a b) a' = if a = a' then b else 0`
(see `Finsupp.single_apply`). -/
DefinitionDoc Finsupp.single as "Finsupp.single"

/-- `Finsupp.single_apply` evaluates `Finsupp.single a b` at a point:

```
(Finsupp.single a b) a' = if a = a' then b else 0
```

After rewriting with this, use `if_pos` or `if_neg` to resolve the
conditional.

**When to use**: Whenever you need to evaluate `Finsupp.single` at a
specific point. -/
TheoremDoc Finsupp.single_apply as "Finsupp.single_apply" in "Finsupp"

NewDefinition Finsupp Finsupp.single
NewTheorem Finsupp.single_apply
TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
