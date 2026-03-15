# W8_ex FinsetExploration -- Playtest Audit Round 1

**World type**: Example (7 levels)
**Predecessor**: W8 FinsetTransformations (8 levels)
**Plan reference**: PLAN.md lines 430-442

---

## 1. Overall Verdict

**NEEDS REVISION.** The world compiles and the proofs are correct, but there are several structural defects: `simp` is not disabled (violating the standard disabled-tactic set), `rintro` is used before it is introduced, L07 deviates from the plan (Boss instead of Transfer), the boss is a gauntlet (four independent replays, no novel integration), `Finset.mem_range` is used but never introduced, and L01/L04 have interactive-proof quality issues for novices. Multiple P0 and P1 items.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Transfer level from plan is missing; replaced with a gauntlet boss. `Finset.mem_range` never introduced. |
| 2. Granularity fit | 3 | Levels are individually well-scoped, but L01 is overloaded (two separate proof strategies in one level) and L07 is a gauntlet. |
| 3. Proof-move teaching | 2 | L04 requires `rintro` and `exact <..., by ..., by ...>` patterns that haven't been taught. L01 also requires `rintro` in its solution. |
| 4. Inventory design | 2 | `simp` not disabled (systemic). `Finset.mem_range` used but never introduced. `rintro` used in L01 but introduced in L04. Missing TacticDoc for disabled tactics. |
| 5. Hint design / recoverability | 3 | Hints are layered (strategy then code). But L04 reverse direction hints suggest `exact <..., by simp, by ring>` which is hostile to interactive exploration. |
| 6. Progression (example->practice->boss) | 2 | Boss is a gauntlet of four independent replays. No transfer level as planned. |
| 7. Mathematical authenticity | 3 | Good concrete examples. Tables in conclusions are helpful. Powerset and product previews are well-motivated. |
| 8. Paper-proof transfer | 2 | Planned transfer level (L07) was replaced with a boss. Transfer moments exist in conclusions but no level forces the learner to articulate. |
| 9. Technical fit | 2 | Missing TacticDocs, missing `Finset.mem_range` introduction, build warnings for `ring` and `rintro` not being introduced in predecessor worlds. |

**Average: 2.3 -- below the 3.0 threshold for "good".**

---

## 3. Coverage Gaps

### P0: `simp` not disabled (systemic)

**All 7 levels** disable `trivial decide native_decide aesop simp_all` but do NOT disable `simp`. The standard disabled set (per project memory) should be `trivial decide native_decide simp aesop simp_all`. Since `simp` is used intentionally with arguments (`simp [Finset.mem_insert, ...]`, `simp only [...]`), the author likely intended it to remain available. However:

- L02: Bare `constructor <;> simp` likely closes the entire goal (membership + non-membership in a small literal finset).
- L03: `ext; simp` may close the filter equality (simp knows `Finset.mem_filter` and can evaluate `x % 2 = 0` for small numerals).
- L05: `simp [Finset.card_powerset]` is a one-shot.
- L06: `simp [Finset.mem_product, Finset.card_product, Finset.mem_insert, Finset.mem_singleton]` is a one-shot.

Since `simp` (with arguments) is part of the intended proof strategy, disabling it entirely may not be appropriate. Instead, consider whether bare `simp` (without arguments) closes goals it shouldn't. If `simp` must stay available, this is P2 (acceptable for an example world where the proofs are concrete). But if bare `simp` one-shots multiple levels, it should be disabled and `simp only` should be used in the intended proofs.

**Recommendation**: Add `simp` to `DisabledTactic` on all levels. The intended proofs all use `simp only [...]` or `simp [specific_lemma]`. Bare `simp` should not be available. Wait -- the proofs use `simp [Finset.mem_insert, Finset.mem_singleton]` (not `simp only`). If `simp` is disabled, these won't work. The fix is to rewrite all `simp [...]` calls to `simp only [...]` and then disable `simp`.

### P0: `Finset.mem_range` used but never introduced

Build warning: "No world introducing Finset.mem_range, but required by FinsetExploration." L01 uses `Finset.mem_range` in its `simp only` call. This theorem should either be introduced with `NewTheorem` in L01 (with a `TheoremDoc`) or in the predecessor W8.

### P0: `rintro` used in L01 before introduction in L04

L01's solution proof (lines 78-79) uses `rintro ⟨a, ha, rfl⟩` and `rintro (rfl | rfl | rfl | rfl | rfl)`. L01's hidden hints explicitly suggest `rintro`. But `rintro` is not declared as `NewTactic` until L04. A learner encountering L01 has no access to or documentation for `rintro`.

**Fix**: Either (a) introduce `rintro` in L01 (add `NewTactic rintro` and `TacticDoc rintro` to L01), or (b) rewrite L01's proof to avoid `rintro` (use `intro h; rcases h with ...` instead).

### P1: `ring` used in L04 backward direction but introduced simultaneously

`ring` is declared as `NewTactic` in L04 alongside its first use. This is technically allowed but means the learner sees `ring` for the first time in a complex context (`exact ⟨_, by simp, by ring⟩`). The first contact with `ring` should be on simpler math.

### P1: L07 plan deviation -- Transfer replaced with Boss

The plan (line 442) specifies L07 as a **Transfer** level: "Describe in words what filter, image, and powerset do to a finite set." The actual L07 is a **Boss** level proving four cardinality facts. The transfer coverage items T8 (S) and T1 (S) from the plan are not addressed.

### P2: No `omega` or `norm_num` disabling

`omega` and `norm_num` are not disabled on any level. For an example world with concrete numerals, `omega` and `norm_num` can close many subgoals. This is less concerning since the intended proofs use `omega` (L03, L01), but `norm_num` could one-shot L05 (`norm_num [Finset.card_powerset]`).

---

## 4. Granularity Defects

### P1: L07 Boss is a gauntlet (Failure Taxonomy #8b)

The boss is a four-part conjunction where each part is an independent replay of an earlier level:
- Part 1 = L03 (filter → card)
- Part 2 = L04 (image → card)
- Part 3 = L05 (powerset card)
- Part 4 = L06 (product card)

There is no interaction between the parts. The learner replays each level's proof in sequence. A boss should require integration -- combining moves in a way that creates a planning or structural challenge beyond replaying individual levels. This boss adds no planning challenge.

**Fix**: Either (a) redesign the boss to require genuine integration (e.g., "filter a product, then image the result, and reason about the final cardinality" -- a chain that requires combining filter, image, and product reasoning in a single proof), or (b) if this is an example world with no true boss, remove the boss label and replace with the planned Transfer level.

### P1: L01 is overbroad

L01 has two separate proof tasks: (1) prove `rfl` for the iterated-insert form, (2) prove a non-trivial `ext`-based equality for the range+image form. Part 2 is substantially harder than Part 1, requires `rintro` (not yet taught), and involves a complex proof with `omega` and witness construction. This is at least two separate lessons crammed into one level.

**Fix**: Split L01 into two levels: L01a (iterated insert = literal, solved by `rfl`, introducing `Finset.range`) and L01b (range+image = literal, teaching the `ext` + membership reasoning pattern on a concrete example).

---

## 5. Learner Simulation

### Attentive Novice

**First stuck point**: L01 part 2, after `ext x` and `simp only [...]`. The goal becomes a biconditional between an existential and a disjunction. The hint says to use `constructor` and then `rintro ⟨a, ha, rfl⟩`. The novice has never seen `rintro`. They will be stuck.

**Most likely wrong move**: In L04, after being told to provide witnesses with `exact ⟨_, by simp, by ring⟩`, the novice tries `use 1` (which works!) but then doesn't know how to close the remaining goals because the hint assumed a different proof shape.

**Hint rescue quality**: L01-L03 hints rescue well within their intended path. L04 hints are too focused on the `rintro`/`exact ⟨...⟩` path and don't support the `use`/`constructor`/`simp` alternative.

**Lesson legibility**:
- L01: Confusing. Two tasks of very different difficulty.
- L02: Clear. Membership/non-membership is well-motivated.
- L03: Clear. `ext` + `simp only` + `omega` is a clean pattern.
- L04: Partially clear. The forward direction (case split) is legible. The backward direction (provide witnesses) is syntactically overwhelming.
- L05: Clear. `rw [card_powerset]; rfl` is elegant.
- L06: Clear. `mem_product` decomposition is well-taught.
- L07: Not a legible boss. Four independent tasks with no unifying thread.

### Experienced Lean User

**Avoidable friction**: L04's backward direction forces five separate `exact ⟨n, by simp, by ring⟩` lines. An experienced user would write `all_goals exact ⟨_, by simp, by ring⟩` or `<;> exact ⟨_, by simp, by ring⟩` but this isn't hinted.

**Alias gaps**: No `rcases` alias for `rintro` in the hint system. No `omega` shortcut mentioned for L04 (which might close goals that `ring` closes).

**Inventory clutter**: `Finset.powerset`, `Finset.card_powerset`, `Finset.product`, `Finset.mem_product`, `Finset.card_product` are all introduced as "preview" items in L05-L06 but may not be needed again until a much later world. This is acceptable for an example world but worth noting.

**Needless verbosity**: L01 part 2 requires the learner to write out `simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]` -- a 4-lemma `simp only` call. This is busywork for a novice.

---

## 6. Boss Integrity Notes

### L07 Boss -- FAIL

**Seeded subskills**: Yes, all four parts were practiced in L03-L06. But this is the problem -- the boss is exactly L03-L06 replayed in sequence.

**Closure quality**: Adequate for the individual parts, poor for integration.

**Integration quality**: None. The four parts share no variables, no hypotheses, no logical dependencies. Each is a self-contained micro-proof. This is a gauntlet (Failure Taxonomy #8b).

**Surprise burden**: None. Every step is a direct replay.

**Could a learner explain why the proof works?** Yes, but only because each part is trivially a copy of an earlier level. A better boss would require the learner to explain *how* the operations interact.

---

## 7. Technical Risks

### Build warnings (P1)

1. **Missing TacticDoc**: `trivial`, `decide`, `native_decide`, `aesop`, `simp_all` all emit "Missing Tactic Documentation" warnings on every level (7 files x 5 warnings = 35 warnings). These should be added in L01 (or in an earlier world).

2. **"No world introducing Finset.mem_range"**: `Finset.mem_range` is used in L01's `simp only` call but has no `NewTheorem` declaration anywhere.

3. **"No world introducing ring"**: `ring` is introduced in L04 as `NewTactic` but the build may warn because it's not introduced in a predecessor world. (Actually it IS introduced here, so this is fine.)

4. **"No world introducing rintro"**: Same situation -- introduced in L04 but used in L01.

### Interactive proof quality (P1)

- **L01 part 2**: After `constructor`, the forward direction requires `rintro ⟨a, ha, rfl⟩; omega` -- a semi-complex one-liner. The backward direction requires `rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩` -- a highly compressed tactic combinator line. These are not suitable for interactive exploration.

- **L04 backward direction**: Five `exact ⟨n, by simp, by ring⟩` lines. Each is an elaborate one-liner requiring the learner to assemble an anonymous constructor with two `by` blocks before getting any feedback. Flag as P1.

---

## 8. Ranked Patch List

| # | Severity | Level | Issue | Fix |
|---|----------|-------|-------|-----|
| 1 | P0 | All | `simp` not in DisabledTactic | Add `simp` to DisabledTactic. Convert `simp [...]` to `simp only [...]` in all proofs. |
| 2 | P0 | L01 | `rintro` used before introduction | Move `NewTactic rintro` + `TacticDoc rintro` to L01, or rewrite L01 proof to use `intro`/`rcases` instead. |
| 3 | P0 | L01 | `Finset.mem_range` used but never introduced | Add `NewTheorem Finset.mem_range` + `TheoremDoc` to L01. |
| 4 | P1 | L07 | Boss is a gauntlet (four independent replays) | Redesign boss for genuine integration, or replace with planned Transfer level (plan says L07 = Transfer). |
| 5 | P1 | L07 | Plan deviation: Transfer level missing | Restore L07 as Transfer level per plan. If keeping boss, add it as L08 and make L07 the transfer. |
| 6 | P1 | L01 | Level is overbroad (two tasks of different difficulty) | Split into two levels: L01a (rfl for insert=literal) and L01b (ext for range+image). |
| 7 | P1 | L04 | `exact ⟨n, by simp, by ring⟩` is interactive-hostile | Break backward direction into `use n` + `constructor` + individual `simp`/`ring` steps. Add hints for each step. |
| 8 | P1 | All | Missing TacticDoc for disabled tactics | Add TacticDoc for `trivial`, `decide`, `native_decide`, `aesop`, `simp_all` in L01. |
| 9 | P2 | L05 | `rfl` one-shots the entire goal | Accept as P2 (cannot disable `rfl`). The intended `rw [card_powerset]; rfl` is pedagogically better and the hint guides toward it. |
| 10 | P2 | L06 | Part 2 (`card_product`) is closable by `rfl` | Accept as P2 (cannot disable `rfl`). The intended `rw [Finset.card_product]` is pedagogically better. |
| 11 | P2 | L04 | `ring` first-contact is too complex | Consider introducing `ring` on a simpler statement first, or accept since it's used inside `by ring` (not standalone). |

---

## 9. What to Playtest Again After Patching

1. **After fixing #1 (simp disabled)**: Re-check that all intended proofs compile with `simp only` instead of `simp [...]`. Verify no level becomes unsolvable.

2. **After fixing #2-#3 (rintro/mem_range)**: Verify L01 still compiles and the hint flow is coherent.

3. **After fixing #4-#5 (boss/transfer)**: Verify the new boss (if kept) has genuine integration. Verify the transfer level (if added) is an actual transfer exercise (not just a conclusion section).

4. **After fixing #6 (L01 split)**: Verify the new L01a and L01b each have coherent dominant lessons. Renumber subsequent levels.

5. **After fixing #7 (L04 interactive quality)**: Verify the broken-up backward direction still compiles and the hints at each step are coherent.

6. **Full pass**: After all fixes, re-run both enrichment and playtest on the revised world.

---

## Summary

The world has good mathematical content and well-chosen concrete examples. The problems are structural:
- **Inventory sequencing** (`rintro` before introduction, `Finset.mem_range` never introduced)
- **Missing tactic disabling** (`simp` available for one-shots)
- **Plan deviation** (Transfer level replaced with gauntlet Boss)
- **Interactive proof quality** (elaborate one-liners in L01 and L04)

Three P0 defects and five P1 defects. Needs revision before the world can be considered complete.
