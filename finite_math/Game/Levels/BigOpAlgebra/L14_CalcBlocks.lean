import Game.Metadata

World "BigOpAlgebra"
Level 14

Title "Chaining Equalities with calc"

Introduction "
# calc Blocks: Multi-Step Equality Proofs

When a proof requires several rewrites in sequence, writing them
as individual `rw` steps works but obscures the logical flow.
The `calc` tactic organizes multi-step equalities into a readable
chain:

```
calc expression₁
    = expression₂ := by proof₁
  _ = expression₃ := by proof₂
```

Each line proves one step of the chain. The `_` refers to the
right-hand side of the previous line. Lean checks that the chain
connects: the first expression on the left, through each
intermediate step, to the final expression.

**Key syntax rules**:
- The first line names the starting expression
- Each subsequent line starts with `_ =` (the underscore is mandatory)
- Each `:= by` opens tactic mode for that step
- You can also use term proofs: `_ = expr₂ := some_lemma`.
  This is shorthand for `_ = expr₂ := by exact some_lemma` — the
  lemma directly proves the equality without entering tactic mode.

**Your task**: Prove that `∑ x ∈ s, (f x + f x) = a + a` using a
calc chain. The proof has two natural steps:
1. Split `∑(f + f)` into `∑f + ∑f` using `sum_add_distrib`
2. Substitute the known value of `∑f`

**Alternative**: You can also solve this with chained `rw` if you
prefer the compact style. Both approaches are valid.
"

/-- Use a calc block to chain equality steps. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) (hf : ∑ x ∈ s, f x = a) :
    ∑ x ∈ s, (f x + f x) = a + a := by
  Hint "Start with `calc ∑ x ∈ s, (f x + f x)` and chain two
  equality steps: (1) apply sum_add_distrib, (2) substitute hf."
  Hint (hidden := true) "The calc block is:
  `calc ∑ x ∈ s, (f x + f x)`
  `    = (∑ x ∈ s, f x) + ∑ x ∈ s, f x := Finset.sum_add_distrib`
  `  _ = a + a := by rw [hf]`"
  Branch
    rw [Finset.sum_add_distrib, hf]
  Branch
    rw [Finset.sum_add_distrib]
    Hint "Good — you've split the sum with `sum_add_distrib`. Now
    substitute the known value of `∑ f` with `rw [hf]`."
    Hint (hidden := true) "Try `rw [hf]`."
    rw [hf]
  calc ∑ x ∈ s, (f x + f x)
      = (∑ x ∈ s, f x) + ∑ x ∈ s, f x := Finset.sum_add_distrib
    _ = a + a := by rw [hf]

Conclusion "
`calc` blocks are the standard way to write multi-step algebraic
proofs in Lean. Each step is individually justified, and the chain
is easy to read.

**Two approaches to this proof**:

The **calc approach** makes each step explicit:
```
calc ∑ x ∈ s, (f x + f x)
    = (∑ x ∈ s, f x) + ∑ x ∈ s, f x := Finset.sum_add_distrib
  _ = a + a := by rw [hf]
```

The **rw approach** is more compact:
```
rw [Finset.sum_add_distrib, hf]
```

Both are valid. `calc` is better for long proofs where readability
matters — the reader sees each intermediate expression. `rw` chains
are better for quick, mechanical transformations where the steps
are obvious.

**Key insight**: `calc` is a proof *organization* tool, not a proof
*discovery* tool. It doesn't give you new power — it gives you
readability. The underlying proof moves (rewriting, substitution)
are the same either way.

In the boss level, you'll choose whichever style you prefer.

**When to use `calc`**:
- Multi-step algebraic manipulations (3+ steps)
- Proofs that others will read
- Any time you want the logical flow to be self-documenting
"

/-- `calc` organizes multi-step equality proofs into readable chains.

## Syntax
```
calc expression₁
    = expression₂ := by proof_step₁
  _ = expression₃ := by proof_step₂
  _ = final_result := by proof_step₃
```

## When to use it
When a proof requires multiple equality-rewriting steps and you
want each intermediate expression to be visible and each step to
be individually justified.

## Key details
- `_` refers to the RHS of the previous step
- Each `:= by` opens tactic mode; you can also use term proofs
- `calc` also works with `≤`, `<`, and mixed relations
-/
TacticDoc «calc»

NewTactic «calc»

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
