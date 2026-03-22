import Game.Metadata

World "Products"
Level 17

Title "Diagonal Decomposition"

Introduction "
# The Self-Product Decomposes

Every pair `(a, b) ∈ s ×ˢ s` either has `a = b` (diagonal) or
`a ≠ b` (off-diagonal). This gives the **decomposition identity**:

$$s.\\text{diag} \\cup s.\\text{offDiag} = s \\times^s s$$

```
Finset.diag_union_offDiag : s.diag ∪ s.offDiag = s ×ˢ s
```

**The `←` rewrite modifier**: When you write `rw [← lemma]`,
Lean rewrites **right-to-left** instead of left-to-right.
This works for **any** lemma of the form `A = B` — not just
`diag_union_offDiag`. Whenever you see the right-hand side of
an equation in your goal and want to replace it with the left-hand
side, `← ` is the tool.

For `diag_union_offDiag`:
- `rw [Finset.diag_union_offDiag]` replaces `s.diag ∪ s.offDiag`
  with `s ×ˢ s` (left → right)
- `rw [← Finset.diag_union_offDiag]` replaces `s ×ˢ s`
  with `s.diag ∪ s.offDiag` (right → left)

**Your task**: Given `hp : p ∈ s.diag ∪ s.offDiag`, prove
`p ∈ s ×ˢ s`. Use the `←` modifier to rewrite the goal.
"

/-- Use reverse rewriting with the decomposition identity. -/
Statement (s : Finset ℕ) (p : ℕ × ℕ) (hp : p ∈ s.diag ∪ s.offDiag) :
    p ∈ s ×ˢ s := by
  Hint "The goal has `s ×ˢ s`. Use `← Finset.diag_union_offDiag`
  to replace it with `s.diag ∪ s.offDiag`."
  Hint (hidden := true) "Try `rw [← Finset.diag_union_offDiag]`.
  This replaces `s ×ˢ s` with `s.diag ∪ s.offDiag` in the goal,
  making it match `hp` exactly."
  rw [← Finset.diag_union_offDiag]
  Hint (hidden := true) "Try `exact hp`."
  exact hp

Conclusion "
The `←` modifier is a general tool for `rw`:

- `rw [h]` where `h : A = B` replaces `A` with `B`
- `rw [← h]` where `h : A = B` replaces `B` with `A`

For `diag_union_offDiag`, the `←` direction is especially
useful: it lets you **decompose** `s ×ˢ s` into its diagonal
and off-diagonal components. This is the direction you'll
need for the boss level.

**Why this matters**: The decomposition `s ×ˢ s = s.diag ∪ s.offDiag`
is a **disjoint union** — diagonal and off-diagonal pairs never
overlap. This means cardinalities add:

$$|s \\times^s s| = |s.\\text{diag}| + |s.\\text{offDiag}|$$
"

/-- `Finset.diag_union_offDiag` states that

`s.diag ∪ s.offDiag = s ×ˢ s`

The diagonal and off-diagonal partition the self-product.

## Syntax
```
rw [Finset.diag_union_offDiag]  -- replaces s.diag ∪ s.offDiag with s ×ˢ s
rw [← Finset.diag_union_offDiag]  -- replaces s ×ˢ s with s.diag ∪ s.offDiag
```

## When to use it
When you need to decompose `s ×ˢ s` into diagonal and
off-diagonal components, or when you need to recognize that
`s.diag ∪ s.offDiag` is the full self-product.
-/
TheoremDoc Finset.diag_union_offDiag as "Finset.diag_union_offDiag" in "Product"

TheoremTab "Product"
NewTheorem Finset.diag_union_offDiag

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
