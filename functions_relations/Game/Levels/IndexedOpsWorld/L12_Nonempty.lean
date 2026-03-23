import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 12

Title "Nonemptiness"

Introduction "
# Set.Nonempty

A set `s` is **nonempty** if it contains at least one element:

$$s \\neq \\emptyset \\;\\Longleftrightarrow\\; \\exists\\, x,\\; x \\in s$$

In Lean, `Set.Nonempty s` is defined as `∃ x, x ∈ s`. To prove a
set is nonempty, you exhibit a witness with `use`.

This is the same move you use for `⋃` (which also reduces to `∃`),
and the same move you use for existential statements in general.
The pattern is always: `use witness`, then prove the witness satisfies
the predicate.

**Your task**: Prove that the set of even natural numbers is nonempty.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty
TheoremTab "Set"

/-- The set of even natural numbers is nonempty. -/
Statement : Set.Nonempty {n : ℕ | Even n} := by
  Hint "`Set.Nonempty s` is defined as `∃ x, x ∈ s`. You need to
  exhibit an even natural number. Use `use` to provide the witness."
  Hint (hidden := true) "`use 0` — zero is even."
  use 0
  Hint "The goal is a set membership that unfolds to `Even 0`.
  Use `show Even 0` to make it explicit."
  Hint (hidden := true) "`show Even 0` then `exact ⟨0, rfl⟩`.

  Recall: `Even n` means `∃ k, n = k + k`. For `n = 0`, the
  witness is `k = 0`, since `0 = 0 + 0`."
  Branch
    exact ⟨0, rfl⟩
  show Even 0
  exact ⟨0, rfl⟩

Conclusion "
You proved nonemptiness by exhibiting a witness. This is the same
`use` move that works for:

| Goal shape | After `use witness` |
|---|---|
| `∃ x, P x` | `P witness` |
| `Set.Nonempty s` | `witness ∈ s` |
| `x ∈ ⋃ i, s i` | `x ∈ s witness` (after `rw [Set.mem_iUnion]`) |

All three are existential statements in disguise. The proof strategy
is always the same: provide the witness, then verify.

**Alternative witnesses**: We used `0`, but `2`, `4`, or any even
number would work. The choice of witness does not matter — only
its existence.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
