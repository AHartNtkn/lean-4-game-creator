import Game.Metadata

World "Products"
Level 6

Title "Dependent Products with Sigma"

Introduction "
# When the Second Component Depends on the First

In `s ×ˢ t`, the two finsets are independent — every first
component is paired with every second component. But what if the
set of valid second components *depends* on which first component
you chose?

`Finset.sigma` handles this:

```
Finset.sigma : Finset ι → (∀ i, Finset (α i)) → Finset (Σ i, α i)
```

Given a finset `s` of indices and a family of finsets `t i` (one
for each index `i`), `s.sigma t` is the finset of dependent pairs
`⟨i, a⟩` where `i ∈ s` and `a ∈ t i`.

**Membership characterization**:
```
Finset.mem_sigma : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1
```

Notice the key difference from `mem_product`: the second condition
is `a.2 ∈ t a.1` — the finset for the second component **depends
on the value of the first component**.

**Your task**: Prove that `⟨1, 3⟩ ∈ s.sigma t` given that
`1 ∈ s` and `3 ∈ t 1`.
"

/-- Prove membership in a sigma construction. -/
Statement (s : Finset ℕ) (t : ℕ → Finset ℕ)
    (h1 : 1 ∈ s) (h2 : 3 ∈ t 1) :
    (⟨1, 3⟩ : Σ _, ℕ) ∈ s.sigma t := by
  Hint "Use `Finset.mem_sigma` to rewrite the goal into a
  conjunction, just like you used `mem_product`."
  Hint (hidden := true) "Try `rw [Finset.mem_sigma]`."
  rw [Finset.mem_sigma]
  Hint "Now you need `1 ∈ s ∧ 3 ∈ t 1`. Both are in your context."
  Hint (hidden := true) "Try `exact ⟨h1, h2⟩`."
  exact ⟨h1, h2⟩

Conclusion "
`Finset.mem_sigma` works just like `Finset.mem_product` — rewrite
to expose the conjunction, then prove each component.

The mathematical difference is important:
- **Product** `s ×ˢ t`: the set of second components is the same
  regardless of which first component you pick
- **Sigma** `s.sigma t`: the set of valid second components
  `t i` can vary with the first component `i`

In combinatorics, sigma appears whenever you count objects whose
structure depends on a parameter — for example, the number of
divisor pairs of `n`, or the number of edges incident to each
vertex in a graph.
"

/-- `Finset.mem_sigma` characterizes membership in `s.sigma t`:

`a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1`

A dependent pair `⟨i, x⟩` belongs to `s.sigma t` iff the index
`i` belongs to `s` and the value `x` belongs to `t i`.

## Syntax
```
rw [Finset.mem_sigma]       -- rewrite sigma membership
rw [Finset.mem_sigma] at h  -- rewrite a hypothesis
```

## When to use it
When the goal or a hypothesis involves `_ ∈ s.sigma t`.

## Key difference from `mem_product`
The second condition is `a.2 ∈ t a.1` (dependent on the first
component), not just `a.2 ∈ t` (independent).
-/
TheoremDoc Finset.mem_sigma as "Finset.mem_sigma" in "Product"

/-- `Finset.sigma` constructs the dependent product of a finset
`s : Finset ι` and a family of finsets `t : ∀ i, Finset (α i)`.

The result is `Finset (Σ i, α i)` — the finset of dependent pairs
`⟨i, x⟩` where `i ∈ s` and `x ∈ t i`.

## Syntax
```
s.sigma t    -- the dependent product
```

## When to use it
When the set of valid second components depends on which first
component is chosen. If the second component is independent,
use `s ×ˢ t` instead.
-/
DefinitionDoc Finset.sigma as "Finset.sigma"

TheoremTab "Product"
NewTheorem Finset.mem_sigma
NewDefinition Finset.sigma

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
