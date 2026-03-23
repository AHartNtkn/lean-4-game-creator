import Game.Metadata

World "SetWorld"
Level 4

Title "An Infinite Set"

Introduction "
# Sets Need Not Be Finite

So far you have seen sets defined by arithmetic bounds like `n < 5`.
But predicates can describe infinite collections too.

The set `{n : ℕ | Even n}` contains all even natural numbers:
$\\{0, 2, 4, 6, 8, \\ldots\\}$ — infinitely many elements.

What does `Even n` mean? It is defined as:
$$\\texttt{Even } n \\;\\;\\Longleftrightarrow\\;\\; \\exists\\, r,\\; n = r + r$$

So `4 ∈ {n | Even n}` unfolds to `Even 4`, which is `∃ r, 4 = r + r`.

To prove an existential `∃ r, P r`, you provide a **witness** — a
specific value of `r` — using the `use` tactic. Here, `use 2` turns
the goal into `4 = 2 + 2`, which is true by computation.

**Your task**: Prove that 4 is even by providing the witness `2`.
Use `use 2`.
"

/-- 4 belongs to the set of even natural numbers. -/
Statement : (4 : ℕ) ∈ {n : ℕ | Even n} := by
  Hint "The goal is `Even 4`, which means `∃ r, 4 = r + r`.
  Provide the witness: `use 2`."
  Hint (hidden := true) "`use 2` substitutes `r = 2` and the remaining
  goal `4 = 2 + 2` is closed automatically by `rfl`."
  use 2

Conclusion "
`use 2` provided the witness $r = 2$ and Lean verified
$4 = 2 + 2$ by computation.

This level illustrates two things:

1. **Sets can be infinite.** The predicate `Even` has no upper bound —
   the set `{n | Even n}` has infinitely many elements. Lean sets
   are just predicates, so finite vs. infinite is not a structural
   distinction.

2. **Existential membership proofs need witnesses.** When the
   membership predicate involves `∃`, you must exhibit a concrete
   value. The `use` tactic is your tool for this.

In ordinary mathematics: *4 is even because 4 = 2 + 2.* That is
exactly what you just proved — no more, no less.
"

/-- `Even n` means there exists `r` such that `n = r + r`.

## Definition
```
Even n ↔ ∃ r, n = r + r
```

## Proof strategy
- To prove `Even n`: provide a witness with `use r`, then show `n = r + r`
- To use `h : Even n`: destructure with `obtain ⟨r, hr⟩ := h` to get the
  witness `r` and equation `hr : n = r + r`

## Examples
- `Even 4` because `4 = 2 + 2` (witness: `r = 2`)
- `Even 0` because `0 = 0 + 0` (witness: `r = 0`)
- `¬ Even 3` because no natural number `r` satisfies `3 = r + r`
-/
DefinitionDoc Even as "Even"

NewDefinition Even

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
