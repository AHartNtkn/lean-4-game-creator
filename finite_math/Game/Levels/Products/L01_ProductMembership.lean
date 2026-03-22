import Game.Metadata

World "Products"
Level 1

Title "Product Membership"

Introduction "
# The Cartesian Product of Finsets

You met `s ×ˢ t` in the Cardinality world and used `card_product`
to count its elements. But you never needed to prove that a
*specific pair* belongs to a product, or to extract the components
of a product membership.

The key characterization is `Finset.mem_product`:

$$
(a, b) \\in s \\times^s t \\iff a \\in s \\land b \\in t
$$

```
Finset.mem_product : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t
```

This is an `↔`, so you can use `rw` to turn a product membership
into a conjunction, or `constructor` after `rw` to split into two
membership goals.

**Your task**: Prove that `(2, 5)` belongs to the product
`{1, 2} ×ˢ {5}`.
"

/-- Prove that a specific pair belongs to a product of finsets. -/
Statement : (2, 5) ∈ ({1, 2} : Finset ℕ) ×ˢ ({5} : Finset ℕ) := by
  Hint "Rewrite with `Finset.mem_product` to turn the product
  membership into two separate membership goals."
  Hint (hidden := true) "Try `rw [Finset.mem_product]`.
  This changes the goal to `2 ∈ s ∧ 5 ∈ t` where `s` and `t` are
  the original finsets."
  rw [Finset.mem_product]
  Hint "Now you have a conjunction. Split it with `constructor`."
  constructor
  Hint "Prove `2 ∈ s` by peeling inserts with `Finset.mem_insert`."
  Hint (hidden := true) "Try `rw [Finset.mem_insert]` then `right`,
  then `rw [Finset.mem_singleton]`."
  · rw [Finset.mem_insert]
    right
    rw [Finset.mem_singleton]
  Hint "Prove `5 ∈ t`."
  Hint (hidden := true) "Try `rw [Finset.mem_singleton]`."
  · rw [Finset.mem_singleton]

Conclusion "
`Finset.mem_product` is the workhorse for reasoning about product
membership. It turns a single membership goal `p ∈ s ×ˢ t` into
two independent membership goals `p.1 ∈ s` and `p.2 ∈ t`.

This is the finset version of the set-theoretic definition:
$s \\times t = \\{(a, b) \\mid a \\in s \\text{ and } b \\in t\\}$.

**Pattern**: `rw [Finset.mem_product]` then `constructor` to split.
"

/-- `Finset.mem_product` characterizes membership in `s ×ˢ t`:

`p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`

A pair belongs to the product iff each component belongs to
the respective finset.

## Syntax
```
rw [Finset.mem_product]       -- rewrite product membership
rw [Finset.mem_product] at h  -- rewrite a hypothesis
```

## When to use it
When the goal or a hypothesis involves `_ ∈ s ×ˢ t`.

## Example
After `rw [Finset.mem_product]`, the goal
`(a, b) ∈ s ×ˢ t` becomes `a ∈ s ∧ b ∈ t`.

## Warning
The `↔` uses `.1` and `.2` (projections), not pattern-matched
`a` and `b`. For a concrete pair `(a, b)`, Lean reduces
`(a, b).1` to `a` automatically.
-/
TheoremDoc Finset.mem_product as "Finset.mem_product" in "Product"

/-- `Finset.product` (written `s ×ˢ t`) is the Cartesian product of
two finsets: the set of all pairs `(a, b)` where `a ∈ s` and `b ∈ t`.

## Syntax
```
s ×ˢ t    -- the Cartesian product
```

## Cardinality
`(s ×ˢ t).card = s.card * t.card` (`Finset.card_product`)

## Key lemma
`Finset.mem_product : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`
-/
DefinitionDoc Finset.product as "Finset.product"

TheoremTab "Product"
NewTheorem Finset.mem_product
NewDefinition Finset.product

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
