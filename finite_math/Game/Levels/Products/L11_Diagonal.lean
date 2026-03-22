import Game.Metadata

World "Products"
Level 11

Title "The Diagonal"

Introduction "
# Diagonal Pairs

Given a finset `s`, its **diagonal** `s.diag` is the set of
'same-element' pairs:

$$s.\\text{diag} = \\{(a, a) \\mid a \\in s\\}$$

The membership characterization is:

```
Finset.mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2
```

Notice the two conditions: the first component must be in `s`,
and both components must be **equal**. This means `s.diag` is a
subset of `s ×ˢ s` — specifically, the pairs on the 'main diagonal.'

**Your task**: Prove that `(3, 3) ∈ s.diag` given `3 ∈ s`.
"

/-- Prove diagonal membership from element membership. -/
Statement (s : Finset ℕ) (h : 3 ∈ s) :
    (3, 3) ∈ s.diag := by
  Hint "Use `Finset.mem_diag` to characterize diagonal membership,
  then prove the two conditions."
  Hint (hidden := true) "Try `rw [Finset.mem_diag]`."
  rw [Finset.mem_diag]
  Hint "The goal is `(3, 3).1 ∈ s ∧ (3, 3).1 = (3, 3).2`, which
  Lean simplifies to `3 ∈ s ∧ 3 = 3`."
  Hint (hidden := true) "Try `exact ⟨h, rfl⟩`."
  exact ⟨h, rfl⟩

Conclusion "
`Finset.mem_diag` characterizes diagonal membership: `(a, b)` is
in `s.diag` iff `a ∈ s` and `a = b`. Equivalently, the diagonal
consists of all pairs `(a, a)` where `a ∈ s`.

**Cardinality**: Since the diagonal has one pair per element of `s`:

$$|s.\\text{diag}| = |s|$$

This is `Finset.diag_card`, which you'll use in the next levels.
"

/-- `Finset.mem_diag` characterizes membership in `s.diag`:

`x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2`

A pair `(a, b)` is in the diagonal iff `a ∈ s` and `a = b`.

## Syntax
```
rw [Finset.mem_diag]
```

## When to use it
When the goal or a hypothesis involves `_ ∈ s.diag`.
-/
TheoremDoc Finset.mem_diag as "Finset.mem_diag" in "Product"

/-- `Finset.diag s` is the diagonal of `s`: the set of pairs
`(a, a)` where `a ∈ s`.

## Cardinality
`s.diag.card = s.card` — one pair per element.
-/
DefinitionDoc Finset.diag as "Finset.diag"

TheoremTab "Product"
NewTheorem Finset.mem_diag
NewDefinition Finset.diag

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
