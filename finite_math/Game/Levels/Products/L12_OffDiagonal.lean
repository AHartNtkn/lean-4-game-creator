import Game.Metadata

World "Products"
Level 12

Title "The Off-Diagonal"

Introduction "
# Off-Diagonal Pairs

The **off-diagonal** `s.offDiag` is the complement of the diagonal
within `s ×ˢ s` — all pairs of *distinct* elements:

$$s.\\text{offDiag} = \\{(a, b) \\mid a \\in s,\\ b \\in s,\\ a \\ne b\\}$$

```
Finset.mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2
```

Three conditions: both components in `s`, and they're different.

**Note on `omega`**: For the third condition (`2 ≠ 5`), the `omega`
tactic handles concrete numeric disequalities — it knows that
distinct natural number literals are different.

**Your task**: Prove that `(2, 5) ∈ s.offDiag` given that both
`2 ∈ s` and `5 ∈ s`.
"

/-- Prove off-diagonal membership from element memberships. -/
Statement (s : Finset ℕ) (h2 : 2 ∈ s) (h5 : 5 ∈ s) :
    (2, 5) ∈ s.offDiag := by
  Hint "Use `Finset.mem_offDiag` to characterize the membership,
  then prove the three conditions."
  Hint (hidden := true) "Try `rw [Finset.mem_offDiag]`."
  rw [Finset.mem_offDiag]
  Hint "You need `2 ∈ s ∧ 5 ∈ s ∧ 2 ≠ 5`. Split with `constructor`
  and handle each part."
  Hint (hidden := true) "Try `constructor` to split the conjunction."
  constructor
  Hint (hidden := true) "The first goal is `2 ∈ s`. Try `exact h2`."
  · exact h2
  Hint "Now you need `5 ∈ s ∧ 2 ≠ 5`. Split again."
  Hint (hidden := true) "Try `constructor`."
  constructor
  Hint (hidden := true) "Try `exact h5`."
  · exact h5
  Hint "Finally, prove `2 ≠ 5`."
  Hint (hidden := true) "Try `omega`."
  · omega

Conclusion "
`Finset.mem_offDiag` has three conditions:
1. `x.1 ∈ s` — the first component is in `s`
2. `x.2 ∈ s` — the second component is in `s`
3. `x.1 ≠ x.2` — the components are distinct

**Contrast with `mem_diag`**: The diagonal requires `x.1 = x.2`;
the off-diagonal requires `x.1 ≠ x.2`. Together they partition
`s ×ˢ s`.

**Cardinality**:
$$|s.\\text{offDiag}| = |s|^2 - |s| = |s| \\cdot (|s| - 1)$$

This counts **ordered** pairs of distinct elements — important
in combinatorics for permutations and arrangements.
"

/-- `Finset.mem_offDiag` characterizes membership in `s.offDiag`:

`x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2`

A pair `(a, b)` is in the off-diagonal iff both `a ∈ s` and
`b ∈ s`, and `a ≠ b`.

## Syntax
```
rw [Finset.mem_offDiag]
```

## When to use it
When the goal or a hypothesis involves `_ ∈ s.offDiag`.
-/
TheoremDoc Finset.mem_offDiag as "Finset.mem_offDiag" in "Product"

/-- `Finset.offDiag s` is the off-diagonal of `s`: the set of
pairs `(a, b)` where `a ∈ s`, `b ∈ s`, and `a ≠ b`.

## Cardinality
`s.offDiag.card = s.card * s.card - s.card`
-/
DefinitionDoc Finset.offDiag as "Finset.offDiag"

TheoremTab "Product"
NewTheorem Finset.mem_offDiag
NewDefinition Finset.offDiag

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
