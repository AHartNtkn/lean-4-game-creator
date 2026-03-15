# W5 FinsetConstructors -- Playtest Audit Round 1

## 1. Overall verdict

**Needs revision.** The world builds and the content is pedagogically coherent, but the boss is completely exploitable (`exact ⟨rfl, rfl, rfl⟩` one-shots it), L07's lesson is bypassed by `decide`, `norm_num` is never disabled and closes L05 (bypassing `cons_eq_insert`), and the boss is a gauntlet (three independent checks with no integration challenge). These must be fixed before the world is clean.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Core construction items introduced and practiced. `Finset.card` introduced but no standalone practice before boss use. |
| Granularity fit | 3 | Each level has one clear lesson. L03 and L04 are slightly similar (both `rfl` on notation desugaring) but justified as progressive complexity. |
| Proof-move teaching | 2 | `rfl` for definitional equality is well taught (L01/L03/L04). But `rw` with a named lemma (L02, L05) is undermined by `rfl`/`norm_num` bypasses. |
| Inventory design | 3 | Items unlocked at appropriate times. `Finset.card`, `Finset.card_singleton`, `Finset.cons`, `Finset.cons_eq_insert`, `DecidableEq`, `Finset.Nonempty` all properly documented. |
| Hint design | 3 | Layered hints (strategy visible, answer hidden) on all levels. L08 has step-by-step hints at each subgoal. No Branch for alternative paths. |
| Progression | 2 | Good L01-L06 ramp, but L07 drifts from the world's theme (nonempty ≠ construction), and the boss is a gauntlet. |
| Mathematical authenticity | 3 | Good treatment of `DecidableEq`, `Finset` vs `Set`, notation desugaring. Concrete examples throughout. |
| Paper-proof transfer | 3 | Each level has "In plain language" sections. Good connection to ordinary math. |
| Technical fit | 2 | Builds cleanly, but `norm_num` exploit path on L05/L08, `decide` exploit on L07, and `rfl` exploit on boss are unaddressed. |

**Average: 2.67.** Below the 3.0 threshold for "good."

## 3. Coverage gaps

| Item | Status | Issue |
|------|--------|-------|
| `Finset.card` (M6 coverage item) | I in L02, G in L08 | No supported practice between intro and boss. Learner never practices `Finset.card` on a 2+ element set before the boss asks for card = 3. |
| `rw` with Finset lemma | I in L02, S in L05 | Both can be bypassed by `rfl`/`norm_num`. The learner may never actually use `rw [Finset.card_singleton]` or `rw [Finset.cons_eq_insert]`. |
| `constructor` for conjunctions | Used in boss | Assumed from NNG4, but boss `exact ⟨rfl, rfl, rfl⟩` bypass means it's never forced. |
| `Finset` vs `Set` (C1) | W in L07 | The warning is textual only. The proof task (proving `Nonempty`) has nothing to do with the `Set`/`Finset` confusion the intro describes. Narrative drift. |

## 4. Granularity defects

### G1. L07 narrative drift (P1)
The intro talks about `Finset` vs `Set` confusion and says "Attempt to apply a Set lemma to a Finset and see why it fails." The actual task is proving `Finset.Nonempty`, which has nothing to do with the claimed lesson. The `Set` vs `Finset` distinction is taught through text, not through the proof. This is failure mode #10 (Narrative drift).

**Fix**: Either redesign L07 to actually demonstrate a `Set` lemma failing on a `Finset` goal (e.g., the learner sees `Set.mem_union` fail and must use `Finset.mem_union`), or honestly re-title and re-intro the level as "Proving a finset is nonempty" and move the `Set` vs `Finset` discussion to a genuine misconception level.

### G2. L03 and L04 near-overlap (P2)
Both levels prove definitional equality by `rfl`. L03: `insert 1 {2} = {1, 2}`. L04: `{1, 2, 3} = insert 1 (insert 2 {3})`. Both are "notation desugaring equals explicit inserts." The difference is only the number of elements. The dominant lesson (desugaring = `rfl`) is the same.

**Mitigating factor**: L03 introduces `insert` and L04 exercises the 3-element case, building familiarity. The overlap is mild and justified by progressive complexity.

### G3. Boss is a gauntlet (P1)
The three conjuncts are independent: (1) notation = explicit inserts, (2) cons = notation, (3) card = 3. The learner can solve each in isolation with no planning. There is no moment where the learner must see the whole structure. This is failure mode #8b (gauntlet boss).

**Fix**: Design a boss that requires genuinely combining construction methods in a single proof -- e.g., construct a finset two ways and prove a property that requires knowing *how* it was constructed (membership reasoning, cardinality argument that depends on non-membership, or a statement where `cons_eq_insert` interacts with a cardinality lemma).

## 5. Learner simulation

### Attentive novice

**First likely stuck point**: L05 (`cons_eq_insert`). The learner sees `Finset.cons 1 {2} h = {1, 2}` and may try `rfl` (which works, bypassing the lesson). If they read the intro, they'll know to use `rw [Finset.cons_eq_insert]`, but the type system doesn't force it. If they try `rfl` first and it works, they never learn about `cons_eq_insert`.

**Most likely wrong move**: On L02, trying `decide` (disabled). The error message will push them toward the correct approach. Good.

**Hint rescue quality**: Hints layer well. Strategy hint first ("What lemma relates cons to insert?"), then code hint hidden ("Try `rw [Finset.cons_eq_insert]`"). The novice can recover.

**Lesson legibility**: Clear on L01-L06. L07 is confusing: the intro talks about `Set` vs `Finset` but the task is about `Nonempty`. The novice may wonder what the Set-vs-Finset discussion has to do with their task.

### Experienced Lean user

**Avoidable friction**: The experienced user will `rfl` through L01, L03, L04, and L05 without reading any hints. They'll `norm_num` or `rfl` through L02. They'll `decide` through L06, L07, and L08. They may close the boss with `exact ⟨rfl, rfl, rfl⟩` in one step. The world teaches them nothing.

**Inventory clutter**: Minimal. Items are introduced cleanly.

**Alias gaps**: None identified. `rfl` and `norm_num` work as expected.

**Forced verbosity**: None. The proofs are short throughout.

## 6. Boss integrity notes

### Seeded subskills
- `rfl`: Introduced L01, practiced L03/L04. Adequate seeding.
- `rw [Finset.cons_eq_insert]`: Introduced L05. Only one use before boss. Borderline -- could use one more practice opportunity.
- `decide`: Introduced L06, used L07. Adequate.
- `constructor`: Assumed from NNG4. Adequate.

### Closure quality
Subskills are present but the boss doesn't force their use. `exact ⟨rfl, rfl, rfl⟩` bypasses everything.

### Integration quality
**Failure**: The boss is a gauntlet. The three parts are independent and don't interact. The learner never needs to plan across parts.

### Surprise burden
None. All moves are taught. (But the boss doesn't force them.)

### Can the learner explain why the proof works?
If the learner uses `exact ⟨rfl, rfl, rfl⟩`: "Everything is true by definition." This is technically correct but doesn't demonstrate understanding of `cons_eq_insert` or `decide` on custom types.

## 7. Technical risks

### T1. Build compiles
Build succeeds. No errors.

### T2. Missing TacticDoc warnings
292 "Missing Tactic Documentation" warnings from the build. These are systemic (pre-existing in earlier worlds) and not specific to W5. The server uses existing docstrings as fallback.

### T3. `norm_num` not disabled (systemic)
`norm_num` is never in any DisabledTactic line in this world. It closes:
- L02 (`card_singleton` goal)
- L03 (`insert` = literal)
- L04 (desugaring)
- L05 (`cons` = `insert` -- **bypasses the lesson**)
- L08 (all three boss parts)

This is a systemic issue. `norm_num` should be added to the DisabledTactic baseline for this world.

### T4. `rfl` closes definitional equalities
`rfl` closes L01 (intended), L02 (bypasses `rw`), L03 (intended), L04 (intended), L05 (bypasses `rw`), and all parts of L08. Cannot disable `rfl`. This is a known P2 limitation (from project lessons learned: "`rfl` on cardinality" is definitionally true, accept as P2).

## 8. Ranked patch list

### P0 (blocking)

**P0-1. Boss exploit: `exact ⟨rfl, rfl, rfl⟩` one-shots the boss.**
The entire boss closes with a single `exact` without using `constructor`, `cons_eq_insert`, or `decide`. The boss teaches nothing in its current form.
**Fix**: Redesign the boss so at least one conjunct is NOT definitionally true. Options:
  - (a) Include a cardinality computation on a custom `DecidableEq` type (like `Color`) where `rfl` fails.
  - (b) Include a non-membership proof (`2 ∉ {1, 3}`) that requires `decide` and can't be solved by `rfl`.
  - (c) Require proving an equality where order differs: `{3, 1, 2} = {1, 2, 3}` (this is NOT `rfl` -- finset equality with different insertion order needs `Finset.ext` or `decide`).
  - (d) Include a membership proof: `1 ∈ Finset.cons 1 (Finset.cons 2 {3} h₁) h₂` that requires `rw [Finset.cons_eq_insert]` followed by `decide` or membership lemmas.

  Option (c) or (d) would force the learner to use taught moves.

### P1 (high)

**P1-1. L07: `decide` bypasses the lesson.**
`decide` one-shots `({1, 2, 3} : Finset Nat).Nonempty`, bypassing the intended `use 1; decide` proof. The learner never learns that `Nonempty` is an existential.
**Fix**: Disable `decide` on L07. The learner must provide a witness with `use`.

**P1-2. L05: `norm_num` bypasses `cons_eq_insert`.**
`norm_num` closes `Finset.cons 1 {2} h = {1, 2}` without using `rw [Finset.cons_eq_insert]`. Also, `rfl` closes it. The intended lesson (learning and using `cons_eq_insert`) is never forced.
**Fix**: Add `norm_num` to DisabledTactic on L05. The `rfl` bypass is P2 (can't disable `rfl`), but at least close the `norm_num` path.

**P1-3. L07 narrative drift: intro claims Set-vs-Finset lesson but task doesn't deliver.**
The intro promises "Attempt to apply a Set lemma to a Finset and see why it fails." The actual task (prove `Nonempty`) has nothing to do with this. The `Set` vs `Finset` distinction is taught via text only.
**Fix**: Either redesign the task to actually involve a Set/Finset confusion (see G1 above), or honestly retitle the level and save the Set-vs-Finset confusion for a level that actually demonstrates it.

**P1-4. Boss is a gauntlet (three independent checks, no integration).**
See G3 above. The three conjuncts don't interact and can be solved independently.
**Fix**: Redesign the boss to require genuine integration -- see P0-1 options.

### P2 (medium)

**P2-1. `norm_num` not in DisabledTactic baseline.**
`norm_num` closes L02, L03, L04 (all also closeable by `rfl`). While `rfl` is the bigger bypass issue on these levels and `norm_num` adds nothing `rfl` doesn't already provide, it should still be disabled for consistency.
**Fix**: Add `norm_num` to DisabledTactic on all levels in this world.

**P2-2. `rfl` closes L02 (bypasses `rw [Finset.card_singleton]`).**
The intended proof is `rw [Finset.card_singleton]`, but `rfl` works because singleton cardinality is definitional. Cannot disable `rfl`. Known limitation.
**Mitigation**: Accept as P2. The intro guides toward `rw` and the learner at least sees the lemma name in the inventory.

**P2-3. No `Finset.card` practice between L02 and L08.**
`Finset.card` is introduced in L02 (singleton, card = 1) and next used in L08 (card = 3). No intermediate practice on a 2-element finset. Coverage jump.
**Fix**: Consider adding a practice level between L06 and L07 that computes `(insert 1 {2}).card = 2` using `Finset.card_insert_of_not_mem`.

### P3 (low)

**P3-1. No `Branch` for alternative proof paths.**
L02 and L05 have `rfl` as an alternative valid proof, but no Branch hint acknowledges this. If a learner tries `rfl` and it works, they get no feedback about the "intended" approach.
**Mitigation**: Since `rfl` is an acceptable proof, a Branch saying "That works too! But the intended approach was..." would be educational. Low priority.

## 9. What to playtest again after patching

After implementing fixes for P0-1, P1-1, P1-2, P1-3, P1-4, and P2-1:
- **L05**: Verify `norm_num` is disabled and `rw [Finset.cons_eq_insert]` is the only path (aside from `rfl`).
- **L07**: Verify `decide` is disabled and `use` + manual membership proof is required.
- **L08 (Boss)**: Full re-audit after redesign. Check all exploit paths on the new statement.
- **All levels**: Verify `norm_num` is disabled everywhere.
- **Build**: Full `lake build` after all changes.
