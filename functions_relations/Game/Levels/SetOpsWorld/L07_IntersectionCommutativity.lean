import Game.Metadata

World "SetOpsWorld"
Level 7

Title "Intersection Commutativity"

Introduction "
# s ∩ t ⊆ t ∩ s

In Level 6, you extracted a single component from an intersection
hypothesis using `.1`. But sometimes you need **both** components.

The `obtain` tactic destructures a conjunction (or intersection
hypothesis) into its parts:

```
obtain ⟨hs, ht⟩ := hx
```

This replaces `hx : x ∈ s ∩ t` with `hs : x ∈ s` and `ht : x ∈ t`.

**Your task**: Prove that intersection is commutative as a subset
relation: `s ∩ t ⊆ t ∩ s`. You need to extract **both** components
from the hypothesis and reassemble them in swapped order using
`constructor`.

**Proof plan**:
1. `intro x hx` — start the subset proof
2. `obtain ⟨hs, ht⟩ := hx` — extract both components
3. `constructor` — split the goal into `x ∈ t` and `x ∈ s`
4. Close each subgoal with the appropriate component
"

/-- The intersection is commutative (subset direction). -/
Statement (α : Type) (s t : Set α) : s ∩ t ⊆ t ∩ s := by
  Hint "Start with `intro x hx` for the subset proof."
  intro x hx
  Hint "`hx : x ∈ s ∩ t` is a conjunction `x ∈ s ∧ x ∈ t`. You need
  both components this time. Use `obtain ⟨hs, ht⟩ := hx` to extract
  them."
  Hint (hidden := true) "`obtain ⟨hs, ht⟩ := hx` gives `hs : x ∈ s`
  and `ht : x ∈ t`. Then `constructor` splits the goal, and you close
  each part with `exact ht` and `exact hs`."
  obtain ⟨hs, ht⟩ := hx
  Hint "Now you have `hs : x ∈ s` and `ht : x ∈ t`. The goal is
  `x ∈ t ∩ s`, which is `x ∈ t ∧ x ∈ s`. Use `constructor` to
  split, then provide each component."
  constructor
  · Hint "The goal is `x ∈ t`. You have `ht : x ∈ t`."
    exact ht
  · Hint "The goal is `x ∈ s`. You have `hs : x ∈ s`."
    exact hs

Conclusion "
You used `obtain` to extract **both** components from an intersection
hypothesis for the first time. This is a move you will use repeatedly:

```
obtain ⟨hs, ht⟩ := hx   -- hx : x ∈ s ∩ t
-- now: hs : x ∈ s, ht : x ∈ t
```

Compare with Level 6, where you only needed one component (`.1`).
When you need both, `obtain` is the right tool.

**`constructor` vs `exact ⟨a, b⟩`**: In Level 5 you saw
`exact ⟨hs, ht⟩` build a conjunction in one shot. In this level you
used `constructor` followed by two `exact` calls. When should you use
which? Use `exact ⟨a, b⟩` when both components are already in context
as hypotheses. Use `constructor` when the subgoals need further tactic
work (e.g., rewriting or case analysis before you can close them).

The full set equality `s ∩ t = t ∩ s` (`Set.inter_comm`) follows by
applying `ext` and using this element-level argument in both directions.
"

/-- `Set.inter_comm` states `s ∩ t = t ∩ s`. -/
TheoremDoc Set.inter_comm as "Set.inter_comm" in "Set"

/-- `inf_comm` is the lattice version of `s ∩ t = t ∩ s`. -/
TheoremDoc inf_comm as "inf_comm" in "Set"

/-- `And.comm` states `a ∧ b ↔ b ∧ a` (propositional commutativity of ∧). -/
TheoremDoc And.comm as "And.comm" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_comm inf_comm And.comm
