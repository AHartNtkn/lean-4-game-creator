import Game.Metadata

World "Products"
Level 7

Title "Concrete Sigma"

Introduction "
# Sigma with Varying Fiber Sizes

`Finset.sigma` really shines when fibers have **different sizes**.
Here's the cardinality formula:

```
Finset.card_sigma : (s.sigma t).card = ∑ a ∈ s, (t a).card
```

Unlike `card_product` (a single multiplication), sigma cardinality
is a **sum** — each index contributes its own fiber size.

**A concrete example**: Imagine a network with 3 nodes indexed by
`Finset.range 3 = {0, 1, 2}`. Node 0 connects to 1 other node,
node 1 connects to 2 others, and node 2 connects to 3 others.
The total number of (node, connection) pairs is the sigma of
the connection sets:

$$1 + 2 + 3 = 6$$

`card_sigma` converts this counting question into a sum that
you can evaluate with familiar tools (`sum_range_succ` and
`sum_range_zero`).

**Your task**: Compute that `(Finset.range 3).sigma t` has
6 elements given the fiber sizes above.
"

/-- Compute a concrete sigma cardinality with varying fiber sizes. -/
Statement (t : ℕ → Finset ℕ)
    (h0 : (t 0).card = 1) (h1 : (t 1).card = 2) (h2 : (t 2).card = 3) :
    ((Finset.range 3).sigma t).card = 6 := by
  Hint "Apply `Finset.card_sigma` to convert the sigma cardinality
  into a sum of fiber sizes."
  Hint (hidden := true) "Try `rw [Finset.card_sigma]`."
  rw [Finset.card_sigma]
  Hint "Now evaluate the sum over `Finset.range 3`. Peel off terms
  from the top with `Finset.sum_range_succ`."
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` to peel off
  the `i = 2` term."
  rw [Finset.sum_range_succ]
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` again for
  the `i = 1` term."
  rw [Finset.sum_range_succ]
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ]` once more
  for `i = 0`."
  rw [Finset.sum_range_succ]
  Hint "The sum over `Finset.range 0` is 0."
  Hint (hidden := true) "Try `rw [Finset.sum_range_zero]`."
  rw [Finset.sum_range_zero]
  Hint "Substitute the known fiber sizes."
  Hint (hidden := true) "Try `rw [h0, h1, h2]`."
  rw [h0, h1, h2]

Conclusion "
$|\\text{sigma}| = \\sum_{i \\in \\{0, 1, 2\\}} |t\\, i| = 1 + 2 + 3 = 6$

The key insight: unlike `s ×ˢ t` where every row has the same
number of columns, a sigma construction can have **different-sized
rows**. The total count is a sum, not a product.

**Where sigma appears in mathematics**:
- **Degree sequences**: if vertex $i$ has $d(i)$ neighbors,
  the total directed edges are $\\sum_i d(i)$
- **Partitions**: items grouped into categories of varying size
- **Fiber bundles**: total space size = sum of fiber sizes

`card_sigma` is the bridge between counting dependent pairs
and evaluating a sum.
"

/-- `Finset.card_sigma s t` states that

`(s.sigma t).card = ∑ a ∈ s, (t a).card`

The cardinality of a dependent product equals the sum of the
fiber cardinalities.

## Syntax
```
rw [Finset.card_sigma]
```

## When to use it
When the goal involves the cardinality of `s.sigma t`.

## Connection to card_product
When `t` is constant (all fibers have the same size), the sum
reduces to multiplication, recovering `card_product`.
-/
TheoremDoc Finset.card_sigma as "Finset.card_sigma" in "Product"

TheoremTab "Product"
NewTheorem Finset.card_sigma

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
