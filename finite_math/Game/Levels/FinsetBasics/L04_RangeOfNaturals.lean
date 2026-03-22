import Game.Metadata

World "FinsetBasics"
Level 4

Title "Range of Natural Numbers"

Introduction "
# Finset.range

`Finset.range n` is the finset $\\{0, 1, 2, \\ldots, n-1\\}$ — the
first `n` natural numbers.

This connects directly to `Fin n` from Phase 1: the elements of
`Finset.range n` are exactly the values that `Fin n` elements can
take. Where `Fin n` gave you typed indices, `Finset.range n` gives
you a set you can reason about with membership.

The membership lemma is `Finset.mem_range`:
$$m \\in \\texttt{Finset.range } n \\;\\longleftrightarrow\\; m < n$$

**Warning**: `Finset.range n` contains $\\{0, \\ldots, n-1\\}$, **not**
$\\{0, \\ldots, n\\}$. The boundary `n` itself is *not* in the range.
This matches `Fin n` (whose elements satisfy `k < n`).

**Your task**: Prove that `3 ∈ Finset.range 5`.

Use `rw [Finset.mem_range]` to convert to `3 < 5`, then `omega`.
"

/-- 3 is in the range {0, 1, 2, 3, 4}. -/
Statement : (3 : ℕ) ∈ Finset.range 5 := by
  Hint "Use `rw [Finset.mem_range]` to convert membership into an inequality."
  rw [Finset.mem_range]
  Hint "The goal is `3 < 5`. Close it with `omega`."
  omega

Conclusion "
The `rw [Finset.mem_range]; omega` pattern is extremely useful.
It reduces finset membership to ordinary arithmetic — territory
you know well from `Fin` proofs.

`Finset.range` appears throughout finite mathematics:
- Summing over `{0, ..., n-1}`: `∑ i ∈ Finset.range n, f i`
- Counting elements satisfying a property in a range
- Connecting `Fin n` indices to set-level reasoning

**Boundary case**: `Finset.range 0 = ∅` — the range with zero
elements is empty. This parallels `Fin 0` being the empty type
from Phase 1. Where `Fin 0` had no inhabitants (no `i : Fin 0`
exists), `Finset.range 0` has no members (no `k ∈ Finset.range 0`).
Same emptiness, different interface.

Remember: `range n` excludes `n` itself. The next level makes
this explicit.
"

/-- `Finset.range n` is the finset `{0, 1, 2, ..., n-1}`.

## Type
`Finset.range : ℕ → Finset ℕ`

## Elements
`Finset.range n` contains exactly the natural numbers `0` through `n - 1`.

## Warning
`Finset.range n` does NOT include `n`. It has `n` elements:
`{0, 1, ..., n-1}`.

## Example
`Finset.range 3 = {0, 1, 2}` (not `{0, 1, 2, 3}`)
-/
DefinitionDoc Finset.range as "Finset.range"

/-- `Finset.mem_range` states that `m ∈ Finset.range n ↔ m < n`.

## Syntax
```
rw [Finset.mem_range]       -- in the goal
rw [Finset.mem_range] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `x ∈ Finset.range n`.
After rewriting, the goal becomes an inequality that `omega` can
typically close.

## Example
```
-- Goal: 3 ∈ Finset.range 5
rw [Finset.mem_range]
-- Goal: 3 < 5
omega
```
-/
TheoremDoc Finset.mem_range as "Finset.mem_range" in "Finset"

NewDefinition Finset.range
NewTheorem Finset.mem_range

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
