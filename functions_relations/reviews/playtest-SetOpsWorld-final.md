# Playtest Review: SetOpsWorld

**Course**: functions_relations
**World**: SetOpsWorld (W03, Lecture)
**Levels**: 16 (L01–L16)
**Date**: 2026-03-23
**Build**: PASS (536 jobs, no errors)

---

## 1. Overall Verdict: PASS

SetOpsWorld is a well-constructed lecture world that teaches the four set operations (∪, ∩, ᶜ, \) as propositional connectives (∨, ∧, ¬, ∧¬). The progression from concrete membership proofs through subset relations to full set equalities is deliberate and well-scaffolded. The boss (distributivity) integrates the core structural moves without introducing new concepts. Exploit blocking is thorough, with lattice aliases and library one-shots systematically disabled. Hints provide rescue paths at every step.

---

## 2. Rubric Scores

| Category | Score | Notes |
|---|---|---|
| Coverage closure | 3 | All four operations covered with intro/support/retrieval/integration. Minor gaps: push_neg/by_contra not in boss; set difference only in L04–L05 |
| Granularity fit | 4 | 16 levels, each with at most one new burden. Clean progression from first-contact to integration to boss |
| Proof-move teaching | 4 | Each new move (left/right, push_neg, by_contra, cases on ∨) explicitly taught with first-contact levels and practiced before use |
| Inventory design | 4 | Thorough DisabledTactic/DisabledTheorem coverage. Lattice aliases blocked. rfl blocked on L05. All new items documented |
| Hint design and recoverability | 3 | Layered hints at every step. Branches for alternative approaches. The `change`+`push_neg` ceremony adds friction that hints explain but cannot simplify |
| Worked example → practice → transfer → boss | 3 | Good progression. Boss integrates 5+ core moves. But push_neg and by_contra are practiced in L11–L15 without reaching the boss |
| Mathematical authenticity | 4 | Operation-to-logic correspondence is the coherent central theme. Conclusions provide paper-proof equivalents. Constructive vs classical distinction (L13–L14) is mathematically honest |
| Paper-proof transfer | 4 | Each conclusion includes informal proof language. The operation-to-logic table builds gradually across L01–L04. L12 conclusion includes a full paper-proof rendering |
| Technical fit and maintainability | 4 | Clean build. Consistent DisabledTactic baseline across all levels. Dependencies correct. No import issues |

**Average**: 3.67 / 4
**Minimum**: 3 / 4

---

## 3. Summary Statistics

- Levels: 16
- New tactics introduced: 4 (left, right, push_neg, by_contra)
- New definitions introduced: 4 (Set.union, Set.inter, Set.compl, Set.diff)
- New theorems introduced: 7 (Set.diff_eq, Set.inter_subset_left, Set.subset_union_left, Set.compl_union, Set.compl_inter, Set.union_compl_self, compl_compl)
- DisabledTactic baseline: trivial decide native_decide simp aesop simp_all tauto norm_num linarith (all levels) + rfl (L05)
- All levels disable Set.mem_setOf_eq and Set.mem_setOf
- All equality levels disable their library theorem + lattice aliases

---

## 4. P0 Defects (blocking)

None.

---

## 5. P1 Defects (high priority)

None.

---

## 6. P2 Defects (medium)

**P2-1. push_neg and by_contra absent from boss**
The world introduces 4 tactics. The boss (distributivity) exercises left/right and cases but never uses push_neg or by_contra. These are extensively practiced in L11–L15 (5 consecutive levels), so the gap is mitigated. The boss was planned as a distributivity proof (no complement involved), which is why these don't appear. Not a design error, but a boss that integrated complement would provide fuller closure.

**P2-2. Set difference appears in only 2 levels (L04, L05)**
After L05 establishes `s \ t = s ∩ tᶜ`, diff never reappears. This is partly by design (diff is reducible to ∩ + ᶜ), and diff will likely recur in PsetSets or later worlds. Minor.

**P2-3. `change` ceremony before `push_neg` on complement hypotheses**
Levels 11, 12, 13, 14 all require `change ¬(...) at hx` before `push_neg at hx` can fire on a complement membership hypothesis. This is a Lean limitation (push_neg needs syntactic `¬`, not definitional), correctly taught and hinted, but adds mechanical friction. No fix available without patching push_neg itself.

---

## 7. Coverage Gaps

| Item | Status | Notes |
|---|---|---|
| ∪ membership (prove) | Full closure | I:L01, S:L08, R:L12, G:L16 |
| ∪ membership (use/cases) | Full closure | I:L10, S:L12/L13, G:L16 |
| ∩ membership (prove) | Full closure | I:L02, S:L05/L07, R:L09, G:L16 |
| ∩ membership (use/obtain) | Full closure | I:L07, S:L09, R:L12/L13, G:L16 |
| ᶜ membership (prove) | Good | I:L03, S:L09, R:L12–L15. Not in boss (by design — boss is distributivity) |
| ᶜ membership (use) | Good | I:L09, S:L12/L13. Not in boss |
| \ membership | Partial | I:L04, S:L05, then gone. OK since L05 reduces to ∩+ᶜ |
| left/right | Full closure | I:L01, S:L08/L10, R:L12/L13, G:L16 |
| push_neg | Good | I:L11, S:L12, R:L13/L14/L15. Not in boss |
| by_contra | Good | I:L13, S:L14/L15. Not in boss |
| ext + constructor (set equality pattern) | Full closure | From SubsetWorld, practiced in L05/L09/L12–L16 |
| obtain (destructure ∩) | Full closure | From SetWorld, practiced in L05/L07/L09, G:L16 |

---

## 8. Granularity Defects

None. Each level is scoped to one dominant lesson. The world has a stable center of gravity (set operations as propositional logic). No level is overbroad or trivially fine.

---

## 9. Learner Simulation Notes

### Attentive novice

- **L01**: First stuck point is knowing to use `left`. The hint fires immediately with the correct suggestion. `show 3 < 5` is needed to unfold membership for omega — this was taught in SetWorld. Recovery path: solid.
- **L05**: First multi-step proof in both directions. Could feel long (ext, constructor, 2 × intro/obtain/exact). Hints rescue at every step. The conclusion explains the `exact ⟨a, b⟩` idiom well.
- **L09**: The move `exact hns hs` (applying a negation to derive False) is genuinely new. Hints explain it. The `contradiction` Branch provides an alternative for students who don't see the function-application interpretation.
- **L10**: First use of `cases h with | inl hs | inr ht`. The novice must learn that `inl`/`inr` are the constructor names for `Or`. The introduction explains this clearly. The focus-dot pattern (`·`) for handling subgoals was established in SubsetWorld.
- **L13**: Two new things simultaneously — `by_contra` and the proof-by-contradiction strategy. These are inseparable: you can't teach the tactic without the strategy. The introduction motivates WHY indirect argument is needed (can't choose left or right without more information). The full hidden hint provides the complete tactic sequence as rescue.
- **L16 (Boss)**: Longest proof in the world (~15 tactic steps). Each individual step has been practiced. The two directions are structurally similar. Hints guide at every fork. The antisymm Branch provides an alternative for students who prefer double-subset over ext.

**Most likely wrong moves**:
- L01: Trying `right` (leads to proving Even 3, which fails — self-correcting)
- L05: Trying `rfl` (disabled — error message says tactic is disabled)
- L11: Trying `push_neg at hx` without `change` first (push_neg may do nothing or give a confusing result — the hint explains the need for `change`)
- L13: Not knowing to use `by_contra` (hint explicitly suggests it)

### Experienced Lean user

- **Avoidable friction**: The `change` ceremony in L11–L14 will annoy experienced users who expect push_neg to handle definitional unfolding. This is a Lean limitation, not an authoring defect.
- **Term-mode shortcuts**: Levels like L06 (`exact hx.1`) and L08 (`left; exact hx`) are already terse. An experienced user might want to write `fun _ hx => hx.1` but the game accepts tactic mode only. Not an issue.
- **Alias gaps**: Thoroughly blocked. Lattice aliases (inf_le_left, sup_comm, etc.) and propositional versions (And.comm, Or.comm, not_or) are all disabled alongside the Set-namespaced versions.

---

## 10. Boss Integrity Notes

**Boss (L16): Intersection distributes over union**

- **Seeded subskills**: All used moves (ext, constructor, obtain, cases on ∨, left/right, exact) were taught and practiced multiple times before the boss.
- **Closure quality**: The boss integrates the 5 core structural moves. It does not test push_neg or by_contra (complement reasoning), which were the focus of L11–L15.
- **Integration quality**: Both directions require 3+ moves each. The forward direction requires obtain + cases + left/right + constructor + exact. The backward direction requires cases + obtain + constructor + left/right + exact. This is genuine integration.
- **Surprise burden**: Zero. Every move in the boss has been practiced. The proof is longer than any single practice level but not overwhelmingly so.
- **Paper-proof readability**: "To show `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`, take any x. Forward: if x ∈ s and x ∈ t ∪ u, then either x ∈ t (so x ∈ s ∩ t, hence in the LHS union via left) or x ∈ u (so x ∈ s ∩ u, via right). Backward: if x ∈ (s ∩ t) ∪ (s ∩ u), case-split: if x ∈ s ∩ t, extract both and build s ∩ (t ∪ u) with left; similarly for s ∩ u with right." A learner can articulate this.
- **Alternative paths**: The antisymm Branch allows a double-subset proof instead of ext+iff. Both paths have hint coverage.

---

## 11. Technical Risks

**Low risk**: The model proofs use `| inl hs =>` syntax (with `=>`) while hints suggest `cases h with | inl hs | inr ht` (without `=>`). The lean4game server matches on goal states, not syntax, so the player's non-`=>` form should produce matching goals. This is the standard pattern used by other lean4game games. Verified: no player-facing text (introductions, hints, conclusions) shows `=>` syntax.

**No risk**: All 16 levels compile. Build exits cleanly. No import cycles.

---

## 12. Ranked Patch List

1. **(P2-1, optional)** Consider adding a 17th level before the boss that combines complement reasoning (push_neg or by_contra) with union/intersection, e.g., prove `s ⊆ t → tᶜ ⊆ sᶜ` (contrapositive for sets). This would give push_neg/by_contra one more retrieval exercise and bridge L15→L16 better. Low priority since L11–L15 already provide 5 levels of practice.

2. **(P2-2, optional)** Consider a level using set difference in a subset context (e.g., `s \ t ⊆ s`) somewhere between L06 and L10, to give diff one more appearance before it fades from the world. Very low priority.

3. **(P2-3, no fix)** The `change`+`push_neg` ceremony is a Lean limitation. No authoring fix possible. The teaching is correct.

---

## 13. What to Playtest Again After Patching

If P2-1 is implemented (adding a contrapositive level before the boss):
- Verify the new level compiles and hints fire correctly
- Verify the boss level number is updated
- Verify the world base file imports are correct
- Re-simulate the novice path through the new level

If P2-2 is implemented (adding a diff-subset level):
- Verify level numbering is consistent
- Check that the new level doesn't repeat the exact pattern of L06 (which is `s ∩ t ⊆ s`)

If no patches are made: no further playtesting needed. The world is ready.
