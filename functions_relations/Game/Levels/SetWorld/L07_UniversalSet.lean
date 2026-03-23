import Game.Metadata

World "SetWorld"
Level 7

Title "Everything is in Set.univ"

Introduction "
# Universal Membership

In Level 1, you proved that a specific `x` belongs to `Set.univ`.
Now prove the stronger statement: **every** natural number belongs
to `Set.univ`.

The statement is `∀ n : ℕ, n ∈ Set.univ`. The proof is the same
pattern as Level 1, but with an `intro` step first.

After `intro n`, the goal becomes `n ∈ Set.univ`, which reduces to
`True`. Then `constructor` closes it — exactly as in Level 1.

**Your task**: Prove the statement.
"

/-- Every natural number belongs to `Set.univ`. -/
Statement : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) := by
  Hint "Start with `intro n` to introduce the universally quantified
  variable."
  intro n
  Hint "The goal is `True` (from `n ∈ Set.univ`). Use `constructor`."
  constructor

Conclusion "
This is the universal counterpart of Level 1: instead of proving
membership for one element, you proved it for all elements.

Compare the two *boundary sets*:

| Set | Predicate | Membership | Proof |
|---|---|---|---|
| `Set.univ` | `fun _ => True` | always `True` | `constructor` |
| `∅` | `fun _ => False` | always `False` | impossible |

These two sets are the extreme cases. Every other set lies between
them: `∅ ⊆ s ⊆ Set.univ` for any `s : Set α`. You will prove these
containments in the next world.
"

/-- `Set.mem_univ x` proves `x ∈ Set.univ` for any `x`. -/
TheoremDoc Set.mem_univ as "Set.mem_univ" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_univ Set.mem_setOf_eq Set.mem_setOf
