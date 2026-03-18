import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 8

Title "The Universal Set"

Introduction
"
The **universal set** `Set.univ` is the set of all elements. In Lean,
`x ∈ Set.univ` is definitionally `True`. Every element belongs to it.

This means every set is a subset of `Set.univ`. After `intro x hx`,
the goal becomes `x ∈ Set.univ`, which is `True`. Use `show True` to
reveal this (retrieving the `show` tactic from Level 1), then close
the goal.

How do you prove `True`? The type `True` has exactly one constructor,
just like the single-element types you may have seen in the Natural
Numbers Game. Use `constructor` — it finds the unique constructor
and closes the goal.

**New definition**: `Set.univ` — the universal set.
"

/-- `Set.univ` is the universal set containing all elements of a type.
For any type `α`, `Set.univ : Set α` is the set where `x ∈ Set.univ`
is definitionally equal to `True`.

Every set is a subset of `Set.univ`. -/
DefinitionDoc Set.univ as "Set.univ"

NewDefinition Set.univ

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem Set.subset_univ le_top

Statement (A : Set ℕ) : A ⊆ Set.univ := by
  Hint "Start with the subset pattern: `intro x hx`."
  intro x hx
  Hint "The goal is `x ∈ Set.univ`. Since `Set.univ` contains everything,
  this is definitionally `True`. Use `show True` to reveal it."
  show True
  Hint "The goal is `True`. This has exactly one constructor (like a
  single-element type). Use `constructor` to close it."
  constructor

Conclusion
"
You proved that every set is a subset of the universal set. The proof
had a nice structure:

1. `intro x hx` — the standard subset opening.
2. `show True` — reveal that `x ∈ Set.univ` is just `True`.
3. `constructor` — close `True` using its unique constructor.

**Key facts**:
- `x ∈ ∅` is definitionally `False` (from Level 7)
- `x ∈ Set.univ` is definitionally `True`
- `∅ ⊆ A` for any set `A` (vacuous truth)
- `A ⊆ Set.univ` for any set `A` (everything is in `Set.univ`)
"
