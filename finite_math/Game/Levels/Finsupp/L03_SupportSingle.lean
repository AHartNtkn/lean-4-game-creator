import Game.Metadata

World "Finsupp"
Level 3

Title "The Support of a Single"

Introduction "
# The Support is a Finset

Every finitely supported function `f : α →₀ M` carries a field
`f.support : Finset α` — the finite set of points where `f` is
nonzero.

For `Finsupp.single a b` with `b ≠ 0`, the support is exactly
the singleton containing `a`:

```
Finsupp.support_single_ne_zero (a : α) (hb : b ≠ 0) :
  (Finsupp.single a b).support = singleton a
```

The condition `b ≠ 0` is essential — if `b = 0`, the function is
zero everywhere and the support would be empty (you'll see this
in the next level).

**Your task**: Prove that the support of `Finsupp.single 3 7` is
the singleton containing `3`.
"

/-- The support of a nonzero single is the singleton. -/
Statement : (Finsupp.single 3 7).support = {3} := by
  Hint "Use `apply Finsupp.support_single_ne_zero` to reduce this to
  proving that the value `7` is nonzero."
  Hint (hidden := true) "Try `apply Finsupp.support_single_ne_zero`.
  This leaves the goal `7 ≠ 0`."
  apply Finsupp.support_single_ne_zero
  Hint "Now prove `7 ≠ 0`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The support of `Finsupp.single a b` is determined by whether `b` is
zero:
- If `b ≠ 0`: the support is the singleton containing `a`
- If `b = 0`: the support is empty (next level)

Since the support is a `Finset`, all the tools you learned in the
Finset worlds — membership, operations, cardinality — apply to
supports of finitely supported functions.

Why does Lean bundle the support as explicit data rather than just
defining it as the set of nonzero values? Because a `Finset` can be
computably iterated over. This is what makes operations like
`Finset.sum` over the support possible — you need to know
*which* elements to sum, and the bundled support tells you.

A plain function `α → M` with a side proof that it has finite support
would let you *reason* about finiteness, but you could not *compute*
with it — you would not be able to enumerate the nonzero positions,
sum over them, or count them. Bundling the support as a `Finset`
makes `Finsupp` a computational object, not just a logical one.

**Pattern**: `apply Finsupp.support_single_ne_zero` then `omega`
to discharge the `b ≠ 0` side condition.
"

/-- `Finsupp.support_single_ne_zero` computes the support of a
nonzero single:

`Finsupp.support_single_ne_zero a (hb : b ≠ 0) :
  (Finsupp.single a b).support = singleton a`

## Syntax
```
apply Finsupp.support_single_ne_zero   -- leaves `b ≠ 0`
exact Finsupp.support_single_ne_zero a hb  -- with proof of `b ≠ 0`
```

## When to use it
When the goal involves `(Finsupp.single a b).support` and you
know `b ≠ 0`.

## Warning
If `b = 0`, the support is empty, not a singleton.
Use `Finsupp.single_zero` instead.
-/
TheoremDoc Finsupp.support_single_ne_zero as "Finsupp.support_single_ne_zero" in "Finsupp"

/-- `f.support` is the `Finset` of points where a finitely supported
function `f` is nonzero.

## Type
If `f : α →₀ M`, then `f.support : Finset α`.

## Key lemma
`Finsupp.mem_support_iff : a ∈ f.support ↔ f a ≠ 0`

## Properties
- `Finsupp.support_zero : (0 : α →₀ M).support = ∅`
- `Finsupp.support_single_ne_zero a hb : (single a b).support = singleton a`
  (when `hb : b ≠ 0`)
-/
DefinitionDoc Finsupp.support as "Finsupp.support"

TheoremTab "Finsupp"
NewTheorem Finsupp.support_single_ne_zero
NewDefinition Finsupp.support

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
