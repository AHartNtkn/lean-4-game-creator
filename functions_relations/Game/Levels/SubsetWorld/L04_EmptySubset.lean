import Game.Metadata

World "SubsetWorld"
Level 4

Title "The Empty Subset"

Introduction "
# Vacuous Truth: ∅ ⊆ s

A fundamental fact in mathematics: the empty set is a subset of every set.

$$\\emptyset \\subseteq s \\quad \\text{for any } s$$

Why? Because `∅ ⊆ s` means `∀ x, x ∈ ∅ → x ∈ s`. This is
**vacuously true**: the premise `x ∈ ∅` is always false (recall from
Set World that `∅` has predicate `fun _ => False`), so the implication
holds no matter what `s` is.

After `intro x hx`, you will have `hx : x ∈ ∅`. Since `x ∈ ∅` is
definitionally `False`, the `contradiction` tactic can detect this
and close the goal immediately — regardless of what the goal is.

**Proof plan**:
1. `intro x hx` — assume some `x ∈ ∅`
2. `contradiction` — `hx` is impossible, so anything follows
"

/-- The empty set is a subset of any set. -/
Statement (α : Type) (s : Set α) : ∅ ⊆ s := by
  Hint "Start with `intro x hx` to introduce an element and assume
  it belongs to `∅`."
  intro x hx
  Hint "`hx : x ∈ ∅` is definitionally `False` — nothing belongs
  to the empty set. Since you have a `False` hypothesis, any goal
  follows. Use `contradiction`."
  Hint (hidden := true) "`contradiction` finds `hx : x ∈ ∅` (which
  is `False`) and closes the goal via *ex falso quodlibet*."
  contradiction

Conclusion "
The proof of `∅ ⊆ s` is a single pattern: assume membership in `∅`,
then observe the assumption is impossible.

This is **vacuous truth**: an implication `P → Q` is true whenever
`P` is false, regardless of `Q`. Here, `P` is `x ∈ ∅` (always false),
so the implication `x ∈ ∅ → x ∈ s` holds for any `s`.

Vacuous truth appears throughout mathematics. The statement
\"every element of ∅ is a purple unicorn\" is true — vacuously.

The library name for this fact is `Set.empty_subset`.
"

/-- `Set.empty_subset s` proves `∅ ⊆ s` for any set `s`. -/
TheoremDoc Set.empty_subset as "Set.empty_subset" in "Set"

/-- `Set.bot_eq_empty` states that `⊥ = ∅` for sets (the lattice bottom is the empty set). -/
TheoremDoc Set.bot_eq_empty as "Set.bot_eq_empty" in "Set"

NewTheorem Set.empty_subset

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.empty_subset Set.mem_setOf_eq Set.mem_setOf Set.bot_eq_empty bot_le OrderBot.bot_le
