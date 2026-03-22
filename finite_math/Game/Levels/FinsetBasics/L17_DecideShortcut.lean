import Game.Metadata

World "FinsetBasics"
Level 17

Title "The decide Shortcut"

Introduction "
# Automation for Concrete Goals

You've been proving membership facts manually: peeling inserts with
`mem_insert`, navigating with `left`/`right`, closing with `rfl`.
This teaches you *what's happening*, but it's tedious for concrete
goals.

Lean has a tactic called `decide` that automatically evaluates
concrete, decidable propositions. Since finset membership is
decidable (Lean can check each element), `decide` can close goals
like `3 ∈ {{1, 2, 3}}` or `4 ∉ {{1, 2, 3}}` in one step.

**When to use decide**:
- The goal involves only **concrete** values (no variables)
- The proposition is **decidable** (membership, equality, etc.)
- You want a quick proof and don't need to show the structure

**When NOT to use decide**:
- The goal involves **variables** — `decide` can't evaluate `i ∈ s`
  when `i` or `s` is unknown
- You want to understand the proof structure

**Your task**: Prove `3 ∈ {{1, 2, 3}}` using just `decide`.
"

/-- Decide closes concrete membership goals automatically. -/
Statement : (3 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) := by
  Hint "`decide` evaluates the membership check computationally
  and closes the goal."
  decide

Conclusion "
`decide` is a convenience tool. It automates what you've been doing
manually — checking each element of a finset for a match. Now that
you understand the structure (insert layers, singleton base, the
`left`/`right` navigation), you can use `decide` as a shortcut for
concrete goals.

The manual approach is still essential when:
- Goals involve **variables** (e.g., `x ∈ s` where `s` is abstract)
- You need to **rewrite** membership into useful forms (e.g., `mem_range`)
- You're proving properties about **arbitrary** finsets

Think of `decide` as the 'calculator mode' for finset membership —
useful for concrete checks, but not a replacement for understanding.

One powerful example: `decide` can prove
`({{1, 2}} : Finset ℕ) = ({{2, 1}} : Finset ℕ)`. This makes the
'unordered' property concrete — the finsets `{{1, 2}}` and `{{2, 1}}`
are literally equal, not just 'the same up to ordering.'

`decide` also works beyond `Finset ℕ`. For example, it can prove
`true ∈ ({{true, false}} : Finset Bool)`. The `Finset` type works for
any type with decidable equality — ℕ, Bool, Fin n, and more.
"

/-- `decide` evaluates decidable propositions by computation.

## Syntax
```
decide
```

## When to use it
When the goal is a concrete, decidable proposition — for example,
membership in a literal finset, equality of concrete numbers, or
boolean predicates applied to specific values.

## When it fails
- Goals involving variables: `decide` cannot evaluate `i ∈ s`
  when `i` or `s` is not fully concrete
- Large computations: `decide` may time out on very large finsets

## Examples
```
-- Goal: 3 ∈ {1, 2, 3}
decide

-- Goal: 5 ∉ {1, 2, 3}
decide

-- Goal: (2 : ℕ) + 3 = 5
decide
```
-/
TacticDoc «decide»

NewTactic «decide»

DisabledTactic trivial native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
