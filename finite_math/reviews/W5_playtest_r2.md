# W5 FinsetConstructors -- Playtest Audit Round 2

## Changes since R1

- World expanded from 8 to 9 levels. New L08 (CardinalityPeeling) teaches `card_insert_of_notMem` + `decide` before the boss, addressing R1-P2-3 (no `card` practice between L02 and boss). Boss moved to L09.
- `decide` disabled on L01-L06 and L09 (boss). Intentionally enabled on L07 (used in intended proof: `use 1; decide`) and L08 (used in intended proof: `rw [card_insert_of_notMem h]; decide`).
- L06 demonstrates `DecidableEq` with a custom `Color` type.
- L07 titled "Finset vs Set" with Nonempty proof as task.
- Boss intro updated to reference L08 for `card_insert_of_notMem`.
- Build passes.

## 1. Overall verdict

**Needs revision.** The R1-P0 (boss exploitable by `exact ⟨rfl, rfl, rfl⟩`) was NOT fixed. All three conjuncts of the boss are still definitionally true, and the boss is still a gauntlet. The new L08 is a strong addition that properly seeds `card_insert_of_notMem`, but L08 itself is one-shottable by `decide` (bypassing the `rw` lesson). `norm_num` is still never disabled and closes 7 of 9 levels. The world has improved structurally but the critical exploit remains.

## 2. Rubric scores

| Category | Score | R1 | Delta | Notes |
|----------|-------|----|-------|-------|
| Coverage closure | 3 | 3 | 0 | L08 closes the `card_insert_of_notMem` practice gap. But `cons_eq_insert` still has only one practice opportunity (L05) before the boss uses it twice. |
| Granularity fit | 3 | 3 | 0 | L08 is well-placed and well-scoped. L07 narrative drift remains (see G1). |
| Proof-move teaching | 2 | 2 | 0 | `rfl` and `norm_num` bypasses remain. L08's `rw` lesson bypassed by `decide`. Boss bypassed by `exact ⟨rfl, rfl, rfl⟩`. |
| Inventory design | 3 | 3 | 0 | `card_insert_of_notMem` now properly introduced in L08 before boss use. No new issues. |
| Hint design | 3 | 3 | 0 | L08 has good layered hints. L09 hints reference L08 correctly. |
| Progression | 3 | 2 | +1 | L08 bridges L02 and the boss, providing practice for the cardinality peeling pattern. The ramp from L01-L09 is smoother. |
| Mathematical authenticity | 3 | 3 | 0 | Unchanged. |
| Paper-proof transfer | 3 | 3 | 0 | L08 conclusion has a good "In plain language" section. |
| Technical fit | 2 | 2 | 0 | `norm_num` not disabled anywhere. `rfl` bypass on boss. `decide` bypass on L08. |

**Average: 2.78.** Still below the 3.0 threshold. The blocking issue is proof-move teaching undermined by exploits.

## 3. Coverage gaps

| Item | Status | Issue |
|------|--------|-------|
| `Finset.card_insert_of_notMem` | I in L08, G in L09 | Properly seeded now. R1-P2-3 resolved. |
| `rw [cons_eq_insert]` | I in L05, G in L09 | Only one practice before boss uses it twice. Borderline. The boss hint walks through it, so acceptable. |
| `norm_num` bypass on proof-move teaching | Systemic | `norm_num` is never disabled. It closes L02, L03, L04, L05, L07, L08, and all three boss conjuncts. This makes proof-move teaching unreliable -- the learner can `norm_num` through the entire world without learning `rfl`, `rw`, or `use`. |
| `decide` bypass on L08 | Not addressed | `decide` one-shots L08 without using `card_insert_of_notMem`. The learner can skip the lesson. |

## 4. Granularity defects

### G1. L07 narrative drift (P2, downgraded from R1-P1)

The level title is "Finset vs Set" and the intro leads with the type distinction. The actual task (prove `Nonempty`) demonstrates the `use` + `decide` pattern, not the Set/Finset confusion. The conclusion does explain the Set/Finset issue well, but the proof task itself doesn't force the learner to experience the confusion.

Downgraded from P1 to P2 because the level *does* teach something useful (the `Nonempty` existential pattern), and the Set/Finset discussion in the intro and conclusion is informative even if the proof doesn't exercise it directly. The intro now honestly describes the task ("Your task: Prove that ..."), which reduces the drift compared to R1.

**Suggested fix**: Rename to "Proving a finset is nonempty" and make the Set/Finset discussion a clearly marked sidebar. Or: add a `sorry`-guarded example that shows a Set lemma failing on a Finset, so the learner *sees* the error even if they don't fix it.

### G2. L03 and L04 near-overlap (P3, downgraded from R1-P2)

Both are `rfl` on notation desugaring. L03 introduces `insert`, L04 extends to 3 elements. The progressive complexity justifies the overlap. No action needed.

### G3. Boss is still a gauntlet (P1, persistent from R1)

The three conjuncts remain independent. Part 1 is `rfl`. Part 2 is `rw [cons_eq_insert]; rw [cons_eq_insert]`. Part 3 is the cardinality peeling chain. There is no moment where the learner must plan across parts or where the parts interact. Adding L08 improved seeding but did not change the boss structure.

**Fix**: See P0-1 below. The boss must be redesigned to require genuine integration.

## 5. Learner simulation

### Attentive novice

**First likely stuck point**: L08 (CardinalityPeeling). The learner sees `(insert 1 {2, 3}).card = 3` and may not know which lemma to apply. The hint says "What lemma lets you peel off the insert?" which is good but vague for a learner who hasn't seen the peeling pattern before. The hidden hint gives the answer. Recovery is adequate.

**Most likely wrong move**: On L05, trying `rfl` first. It works, so the learner never learns `cons_eq_insert`. Then in the boss, they try `rfl` on the cons part (Part 2) and it works again. The `cons_eq_insert` lesson is never actually learned.

**Hint rescue quality**: Hints are layered throughout. L08's hints are particularly good (strategy first, then code). The boss hints walk through each part. Good rescue for genuine learners.

**Lesson legibility**: Clear on L01-L06 and L08. L07's dual focus (Set vs Finset title + Nonempty task) could confuse the novice about what they are supposed to learn. L09 (boss) is clear about integration.

### Experienced Lean user

**Avoidable friction**: The experienced user will `rfl` through L01, L03, L04, L05, L06. They will `norm_num` through L02. They will `decide` through L07 and L08. They will `exact ⟨rfl, rfl, rfl⟩` through L09. **The experienced user learns nothing from this world.**

**Critical path**: `norm_num` closes L02, L03, L04, L05, L07, L08, and all boss parts. The only level where `norm_num` fails is L01 (the empty finset). An experienced user could `norm_num` through 8 of 9 levels.

**Inventory clutter**: Minimal. Items are introduced cleanly and at the right times.

## 6. Boss integrity notes (L09)

### Seeded subskills
- `rfl` for definitional equality: Introduced L01, practiced L03/L04/L06. Adequate seeding.
- `rw [Finset.cons_eq_insert]`: Introduced L05. One practice before boss uses it twice. Borderline but acceptable with hints.
- `rw [Finset.card_insert_of_notMem]`: Introduced L08. One practice before boss. Adequate (L08 teaches the pattern, boss applies it twice).
- `rw [Finset.card_singleton]`: Introduced L02 as the level's main tool. Adequate.
- `constructor`: Assumed from NNG4. Fine.

### Closure quality
Subskills are present and seeded. The R1 gap (no `card_insert_of_notMem` practice) is resolved.

### Integration quality
**Still failing.** The boss is a gauntlet (failure mode #8b). The three parts are solved independently. No part requires awareness of the other parts. The boss does not create a novel planning challenge beyond replaying L04 + L05 + L08.

### Surprise burden
`card_insert_of_notMem` requires supplying the correct hypothesis argument (e.g., `rw [Finset.card_insert_of_notMem h₃]` not just `rw [Finset.card_insert_of_notMem]`). This was taught in L08, which supplies `h` as a hypothesis. The boss provides `h₃` and `h₄`. The naming difference is minimal surprise. The boss hints explicitly name the hypotheses to use. Acceptable.

### Can the learner explain why the proof works?
If the learner uses `exact ⟨rfl, rfl, rfl⟩`: "Everything is true by definition." This is technically correct but demonstrates zero understanding of `cons_eq_insert`, `card_insert_of_notMem`, or the structural cardinality reasoning the world exists to teach.

If the learner follows the hints: "The notation and explicit inserts are the same by definition. The cons-built finset equals the insert-built one by `cons_eq_insert`. The cardinality is computed by peeling off inserts one at a time, using `card_insert_of_notMem` for each layer, then `card_singleton` for the base." This demonstrates the full repertoire. But the type system does not force this path.

## 7. Technical risks

### T1. `norm_num` not disabled (P1 -- PERSISTENT from R1)

`norm_num` is absent from every `DisabledTactic` line in this world. It closes L02, L03, L04, L05, L07, L08, and the boss. On L05, `norm_num` closes the goal without even needing `[Finset.cons_eq_insert]` as a hint -- it figures out the conversion automatically.

This is the most impactful single-tactic bypass in the world. Adding `norm_num` to the DisabledTactic baseline would close 6+ exploit paths in one change.

### T2. `decide` one-shots L08 (P1 -- NEW)

L08 intentionally enables `decide` for its second step (`rw [card_insert_of_notMem h]; decide`). But `decide` also one-shots the entire goal without the `rw`, because the cardinality of a concrete finset is decidable. The learner can skip the `card_insert_of_notMem` lesson entirely.

**Options**:
- (a) Disable `decide` on L08 and use `rfl` or `norm_num` (but those are also bypasses).
- (b) Change L08's statement to use a larger finset or a type variable where `decide` is slower or fails.
- (c) Accept as P2 since the boss forces the peeling pattern anyway. But -- the boss is also exploitable, so this doesn't help.

### T3. `rfl` closes all definitional equalities (P2 -- known limitation)

`rfl` closes L01, L02, L03, L04, L05, L06, and all boss parts. Cannot disable `rfl`. Known from R1.

### T4. Boss exploit: `exact ⟨rfl, rfl, rfl⟩` (P0 -- PERSISTENT from R1)

The R1 P0-1 was listed as fixed but was NOT fixed. The boss statement remains:
```
    ({1, 2, 3} : Finset Nat) = insert 1 (insert 2 (insert 3 ∅)) ∧
    Finset.cons 1 (Finset.cons 2 {3} h₁) h₂ = ({1, 2, 3} : Finset Nat) ∧
    ({1, 2, 3} : Finset Nat).card = 3
```

All three conjuncts are definitionally true:
- Part 1: notation desugaring = `rfl`
- Part 2: `cons` of concrete values = `rfl` (Lean reduces `cons` to `insert` internally)
- Part 3: `card` of a concrete finset = `rfl` (Lean evaluates it)

Verified by compilation: `exact ⟨rfl, rfl, rfl⟩` closes the entire boss.

### T5. Duplicate `TheoremDoc` risk

`Finset.card_insert_of_notMem` has `TheoremDoc` and `NewTheorem` in L08 only (L09 has neither). No duplicate. Clean.

### T6. Build status

Build passes. 292 pre-existing "Missing Tactic Documentation" warnings (systemic, not W5-specific).

## 8. Ranked patch list

### P0 (blocking)

**P0-1. Boss exploit: `exact ⟨rfl, rfl, rfl⟩` one-shots the boss.** (PERSISTENT from R1)

This was reported in R1 as P0-1 and described as fixed in the R2 context ("Boss redesigned with structural cardinality proof requiring `card_insert_of_notMem` + `card_singleton`"). However, the boss statement is unchanged and all three parts remain definitionally true. The intended proof uses `card_insert_of_notMem` but nothing forces the learner to use it.

**Fix**: At least one conjunct must NOT be definitionally true. Concrete options:

- **(a) Finset equality with different insertion order**: Replace Part 1 with `({3, 1, 2} : Finset Nat) = {1, 2, 3}`. This is NOT `rfl` -- different insertion order means different `insert` chains. Requires `Finset.ext` or `decide`. This forces non-trivial reasoning.

- **(b) Cardinality with generic type**: Replace Part 3 with cardinality of a finset built from a custom type (e.g., `Color`) where the kernel cannot evaluate `card` definitionally. This would force the structural peeling proof.

- **(c) Non-membership as an explicit goal**: Add a conjunct requiring `(4 : Nat) ∉ ({1, 2, 3} : Finset Nat)` where `rfl` fails. But `decide` handles this (and `decide` is disabled on the boss), so this is stronger.

- **(d) Combine cons and cardinality**: Make the cardinality goal reference the cons-built finset directly: `(Finset.cons 1 (Finset.cons 2 {3} h₁) h₂).card = 3`. This might still be `rfl` but is worth testing.

Option (a) is the simplest and most directly addresses the gauntlet problem by making Part 1 require actual work (not `rfl`). Combined with disabling `norm_num`, this forces the learner to engage.

### P1 (high)

**P1-1. `norm_num` not disabled on any level.** (PERSISTENT from R1)

`norm_num` is absent from every DisabledTactic line. It closes L02 through L09 (everything except L01). Adding `norm_num` to the standard DisabledTactic baseline (`trivial decide native_decide simp aesop simp_all norm_num`) across all 9 levels closes the largest single exploit vector.

**Fix**: Add `norm_num` to the DisabledTactic line on all 9 levels.

**P1-2. `decide` one-shots L08, bypassing the `card_insert_of_notMem` lesson.** (NEW)

L08 enables `decide` for its second step, but `decide` also closes the goal in one shot without the `rw`. The learner can skip the entire `card_insert_of_notMem` lesson that L08 exists to teach.

**Fix**: Disable `decide` on L08 and change the intended proof so the second step uses `rfl` instead (after the `rw`, the remaining goal `2 + 1 = 3` is `rfl`). The proof becomes `rw [Finset.card_insert_of_notMem h]; rfl`. Update hints accordingly.

**P1-3. Boss is a gauntlet.** (PERSISTENT from R1)

The three conjuncts are independent. No integration challenge exists. This is failure mode #8b.

**Fix**: Redesign boss to include at least one conjunct that requires combining moves from different levels. See P0-1 options -- option (a) (different insertion order) inherently requires the learner to think about finset equality in a new way, creating genuine integration.

### P2 (medium)

**P2-1. L07 narrative drift.** (PERSISTENT from R1, downgraded from P1)

Title says "Finset vs Set" but the proof task is "prove Nonempty." The learner reads about Set/Finset confusion but never experiences it. The text is informative but the task doesn't deliver on the title's promise.

**Fix**: Either rename to "Proving a finset is nonempty" or redesign to actually demonstrate a Set lemma failing.

**P2-2. `rfl` closes L02 and L05, bypassing `rw` lessons.** (PERSISTENT from R1)

L02's intended `rw [card_singleton]` and L05's intended `rw [cons_eq_insert]` are both bypassed by `rfl`. Cannot disable `rfl`. Known limitation.

**Mitigation**: Accept. The intros and hints guide toward the intended approach. The learner who reads the material will learn the lemma names even if `rfl` also works.

### P3 (low)

**P3-1. No `Branch` for `rfl` alternative paths.** (PERSISTENT from R1)

L02 and L05 accept `rfl` but provide no Branch hint acknowledging this alternative. Low priority since `rfl` is a valid proof.

## 9. What to playtest again after patching

After implementing P0-1 (boss redesign), P1-1 (disable `norm_num`), and P1-2 (disable `decide` on L08):

1. **All 9 levels**: Verify `norm_num` is disabled everywhere and no new exploit path opens.
2. **L08**: Verify `decide` is disabled, `rfl` closes after `rw`, and hints updated for `rfl` instead of `decide`.
3. **L09 (Boss)**: Full re-audit of the redesigned boss:
   - Check all one-shot exploit paths (`rfl`, `exact ⟨...⟩`, `norm_num`, `decide`).
   - Verify integration challenge is genuine.
   - Check hint coverage for the new boss structure.
   - Simulate novice walkthrough of the new boss.
4. **L07**: If renamed, verify the new title/intro are coherent.
5. **Build**: Full `lake build` after all changes.

## Summary of R1 items

| R1 Item | Status | Notes |
|---------|--------|-------|
| P0-1 Boss exploit | **NOT FIXED** | `exact ⟨rfl, rfl, rfl⟩` still works |
| P1-1 L07 decide bypass | Fixed | `decide` disabled on L07... but `norm_num` bypass remains |
| P1-2 L05 norm_num bypass | **NOT FIXED** | `norm_num` still not disabled anywhere |
| P1-3 L07 narrative drift | Partially addressed | Intro more honest, but title and structure still drift |
| P1-4 Boss gauntlet | **NOT FIXED** | Still three independent parts |
| P2-1 norm_num baseline | **NOT FIXED** | `norm_num` still absent from all DisabledTactic lines |
| P2-2 rfl on L02 | Accepted P2 | Cannot disable rfl |
| P2-3 No card practice | **FIXED** | L08 CardinalityPeeling added |
| P3-1 No Branch hints | Persistent | Low priority, unchanged |
