# Playtest Audit R4: W3_ex (FinThreeExamples)

**Auditor**: playtest-auditor
**Date**: 2026-03-15
**Round**: 4 (re-audit after R3 trivial fix)
**World files**: `Game/Levels/FinThreeExamples/L01_Enumerate.lean` through `L11_Boss.lean` (11 levels)
**Build status**: Compiles (`lake build` succeeds, 8125 jobs, no errors)
**Predecessor worlds**: FinIntro (12 levels), FinCompute (11 levels)
**World role**: Example / case-study world for `Fin 3`

---

## 1. Overall Verdict

**PASS**

The R3 P0 defect (`trivial` exploiting all 11 levels) has been fixed. `trivial` now appears in the `DisabledTactic` list of every level. The build succeeds. No remaining single-tactic exploit bypasses a level's intended lesson in a way that a novice learner would discover. The world is structurally sound, pedagogically coherent, and well-documented.

Two carried-forward P1 issues remain (L04 compound reference proof, L08 `rfl` exploitability). Neither is blocking. See details below.

### R3 defect resolution status

| R3 defect | Severity | Status | Evidence |
|-----------|----------|--------|----------|
| `trivial` exploits all 11 levels | P0 | **FIXED** | `trivial` now in `DisabledTactic` on all 11 levels. Verified by grep: all 11 files contain `trivial` in their `DisabledTactic` line. |
| L04 compound one-liner reference proof | P1 | **CARRIED FORWARD** | Reference proof still uses `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)`. Mitigated by introduction text and hints describing step-by-step approach. |

### Changes since R3

| Change | Assessment |
|--------|-----------|
| `trivial` added to `DisabledTactic` in all 11 levels | Correct and effective. No build issues. |

---

## 2. Rubric Scores

| Category | Score | R3 Score | Notes |
|----------|-------|----------|-------|
| 1. Coverage closure | 3 | 2 | All items have proper declarations. `trivial` exploit fixed. Intended proof paths are the only viable paths for novices. Minor gap: `Fintype.card` introduced in L01 but not used until L08 (early preview). |
| 2. Granularity fit | 4 | 4 | 11 levels with clear progression. Each level has one dominant lesson. No level is too broad or too fine. |
| 3. Proof-move teaching | 3 | 2 | With `trivial` blocked, the intended proof moves are effectively taught. L04 compound closer is a minor interactive quality issue but does not prevent learning. |
| 4. Inventory design | 3 | 3 | All new items documented. `TacticDoc trivial` is missing (build warning but not error). New tactics, definitions, and theorems are well-documented and timely. |
| 5. Hint design and recoverability | 3 | 3 | Layered hints throughout. Strategy hints visible, code hints hidden. Per-case hints in L01, L05, L06, L09, L11. No `Branch` alternatives for `use` vs `refine` in L03. |
| 6. Progression | 4 | 4 | Excellent arc from warm-up through positive/negative properties, counting, integration, enrichment, to boss. Support faded well. |
| 7. Mathematical authenticity | 4 | 4 | Rich concretization of abstract definitions. Dual pigeonhole preview (L06/L07). Involution/order concept (L10). Transfer language in every conclusion. Permutation enumeration in L11 conclusion. |
| 8. Paper-proof transfer | 4 | 4 | Plain-language translations in all 11 conclusions. Comprehensive skills table in L11. The world consistently connects Lean proofs to informal reasoning. |
| 9. Technical fit and maintainability | 3 | 2 | Compiles cleanly. Dependencies correct. `trivial` fix resolves the technical undermining. One build info warning about missing `TacticDoc trivial`. |

**Average**: 3.4 (up from 3.1)
**Minimum**: 3 (all categories at 3 or above)

**Verdict**: Meets the quality bar. Average >= 3, no category below 2, and no automatic red flags after `trivial` fix.

---

## 3. Statement Exploitability (Critical Check)

### 3a. `trivial` verification

| Level | `trivial` in `DisabledTactic`? | Verified |
|-------|-------------------------------|----------|
| L01 | YES | `DisabledTactic trivial decide native_decide omega simp aesop simp_all` |
| L02 | YES | `DisabledTactic trivial decide native_decide omega simp aesop simp_all` |
| L03 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all` |
| L04 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all` |
| L05 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num` |
| L06 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all` |
| L07 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all` |
| L08 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num` |
| L09 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num` |
| L10 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all omega norm_num` |
| L11 | YES | `DisabledTactic trivial decide native_decide simp aesop simp_all omega norm_num` |

**All 11 levels disable `trivial`.** R3 P0 is resolved.

### 3b. Missing `TacticDoc trivial`

The build produces a warning: `Missing Tactic Documentation. Using existing docstring. Add trivial`. This means:
- The `DisabledTactic trivial` IS effective (the game server blocks the tactic)
- The player sees a fallback docstring for `trivial` (from Lean core) rather than a course-specific explanation
- This is a P2 UX issue, not a blocking problem

### 3c. Complete exploit vector table

| Tactic | Disabled? | Can close any level if enabled? | Risk |
|--------|-----------|-------------------------------|------|
| `trivial` | All 11 | Yes (all 11) | **BLOCKED** |
| `decide` | All 11 | Yes (most) | **BLOCKED** |
| `native_decide` | All 11 | Yes (most) | **BLOCKED** |
| `simp` | All 11 | Yes (many) | **BLOCKED** |
| `simp_all` | All 11 | Yes (many) | **BLOCKED** |
| `aesop` | All 11 | Yes (many) | **BLOCKED** |
| `omega` | L01, L02, L10, L11 | L01, L02 | **BLOCKED** where needed |
| `norm_num` | L05, L08, L09, L10, L11 | See 3d below | Partially blocked |
| `tauto` | None | No (fails on all tested statements) | No risk |
| `linarith` | None | No (fails on L01) | No risk |
| `ring` | None | No (wrong domain) | No risk |
| `rfl` | Cannot be disabled | L08 only (see 3e) | P2 |
| `assumption` | None | No | No risk |
| `contradiction` | None | No | No risk |

### 3d. `norm_num` with explicit lemma arguments

`norm_num [Fin.forall_fin_succ]` closes L01 and L02 (where `norm_num` is NOT disabled). However:
- Bare `norm_num` (without lemma arguments) does NOT close L01 or L02. Verified.
- The learner would need to know the specific Mathlib lemma `Fin.forall_fin_succ` to exploit this.
- `Fin.forall_fin_succ` is not taught in the course and does not appear in the player's theorem panel.
- A novice would not discover this. An experienced Lean user might, but they would already understand the lesson.

**Verdict**: P2 (expert-only exploit requiring untaught library knowledge). Not blocking.

### 3e. `rfl` on L08

`Fintype.card (Fin 3 x Fin 3) = 9` is definitionally true in Lean 4. `rfl` closes L08 in a single step. Verified.

This bypasses the intended lesson (learning `Fintype.card_prod` and `Fintype.card_fin` as rewrite lemmas). However:
- `rfl` is a baseline NNG4 tactic. Disabling it would break the course.
- The introduction guides the learner to use `rw [Fintype.card_prod]` then `rw [Fintype.card_fin]`.
- The LESSON is the generalizable method (rewriting with cardinality lemmas), not the specific answer (9).
- A learner who types `rfl` gets the right answer but misses the method. The hints redirect.
- No other level in this world is closable by bare `rfl` (verified: `rfl` fails on L01, L04, L10).

**Verdict**: P2 (inherent to the statement type; unavoidable without reformulation). The pedagogical content is in the method, and hints guide the method. Not blocking.

### 3f. No `DisabledTheorem` used

No `DisabledTheorem` entries exist in this world. This means any Mathlib theorem is available via `exact` or `rw`. However, no single Mathlib theorem was found that closes any level's goal directly (the statements are specific enough that library lemmas don't match exactly). No risk identified.

---

## 4. Interactive Proof Quality

| Level | Intended proof steps | Interactive? | Notes |
|-------|---------------------|-------------|-------|
| L01 | `intro i` -> `fin_cases i` -> 3x (`left`/`right` + `rfl`) | Yes | Each step gives visible feedback |
| L02 | `intro i` -> `fin_cases i` -> 3x `norm_num` | Yes | Clear step-by-step |
| L03 | `refine <(0,1), ?_>` -> `intro h` -> `have hv` -> `norm_num at hv` | Yes | Four distinct steps |
| L04 | `intro a b h` -> compound closer | **P1** | Reference proof is compound `<;>` one-liner. Hints describe step-by-step. **Carried from R2/R3.** |
| L05 | `intro b` -> `fin_cases b` -> 3x `exact <_, rfl>` | Yes | Clean |
| L06 | `intro h` -> `obtain` -> compound closer | Acceptable | `obtain` expression is coached by hint |
| L07 | `intro h` -> `have h03` -> `have :=` -> `norm_num at this` | Yes | Excellent interactive flow |
| L08 | `rw [card_prod]` -> `rw [card_fin]` | Yes | Two clean rewrites (or `rfl` bypass, see 3e) |
| L09 | `constructor` -> inj block -> surj block | Yes | Integration of L04+L05 |
| L10 | `intro i` -> `fin_cases i` -> 3x `rfl` | Yes | Simple and appropriate for concept-focused level |
| L11 | `constructor` -> inj block -> surj block | Yes | Boss uses same interactive structure as L09 |

**L04 P1 (carried forward)**: The reference proof `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)` requires the learner to compose the compound expression before seeing feedback. The introduction text describes the step-by-step method and the per-case closer pattern. The hidden hint gives the compound version as an optimization. The step-by-step path (handling each of the 9 goals individually) works but has no per-case hints after `fin_cases a <;> fin_cases b`. This is mitigated by the detailed introduction.

---

## 5. Coverage Sanity

### 5a. Coverage closure assessment

| Item | Axis | Coverage states | Assessment |
|------|------|-----------------|------------|
| `Fin 3` concretization | EXAMPLE | I (L01), S (L02-L09), G (L10, L11) | Strong |
| `fin_cases` retrieval | MOVE/LEAN | R (L01-L07, L10), G (L09, L11) | Strong |
| Disjunction navigation (`left`/`right`) | MOVE/LEAN | I (L01) only | Weak closure but acceptable for example world |
| `congr_arg Fin.val h` contradiction | MOVE | I (L03), S (L04), R (L07), G (L11) | Strong |
| `Function.Injective` | MATH | I (L04), R (L09), G (L11) | Adequate |
| `Function.Surjective` | MATH | I (L05), counterexample (L06), R (L09), G (L11) | Strong |
| `Function.Bijective` | MATH | I (L09), G (L11) | Adequate |
| Function composition / involution | MATH | I (L10) | Preview; retrieval expected in later worlds |
| `obtain` for existential destruction | LEAN | I (L06) | Introduced; retrieval in later worlds |
| `Fintype.card_prod`, `Fintype.card_fin` | MATH/LEAN | I (L08) | Preview for counting worlds |
| Pigeonhole preview | TRANSFER | L06, L07 | Good narrative setup |

### 5b. Coverage gaps (non-blocking)

1. `left`/`right` are introduced in L01 but never retrieved in this world. Acceptable -- they are general-purpose tactics that will recur in many future worlds.
2. `Fintype.card` is introduced as a NewDefinition in L01 but used only in L08. The 7-level gap creates inventory clutter. P3 suggestion: move the `NewDefinition Fintype.card` to L08 where it's first used.
3. No counterexample for bijectivity (e.g., "this function is NOT bijective"). The dual pair L06/L07 covers injectivity and surjectivity failures separately, which implicitly covers bijection failure.

---

## 6. Granularity Sanity

### 6a. Level-by-level assessment

All 11 levels pass the one-sentence test (each level has one identifiable dominant lesson). No level is too broad or too fine.

### 6b. World coherence

The world has a coherent center of gravity: **concrete reasoning about functions on `Fin 3` via exhaustive case analysis**. The 11-level progression is:

1. L01-L02: Warm-up (retrieving `fin_cases` on concrete tasks)
2. L03: Construction (existential witness with constraint)
3. L04-L05: Positive function properties (injectivity, surjectivity)
4. L06-L07: Negative function properties (counterexample thinking)
5. L08: Counting (cardinality of products)
6. L09: Integration (bijectivity = inj + surj)
7. L10: Enrichment (involution -- new concept, familiar proof shape)
8. L11: Boss (same skills, different function)

No splitting needed. The world covers one coherent theme with steady escalation.

### 6c. Boss seeding

All boss subskills are seeded:

| Subskill | Where seeded | Boss usage |
|----------|-------------|------------|
| `constructor` to split conjunction | L09 | First step |
| `intro a b h; fin_cases a <;> fin_cases b` | L04, L09 | Injectivity |
| `exfalso; congr_arg Fin.val h; norm_num at this` | L03, L04, L07, L09 | Off-diagonal cases |
| `rfl` for diagonal cases | L04, L09, L10 | Diagonal cases |
| `intro b; fin_cases b; exact <_, rfl>` | L05, L09 | Surjectivity |

No lottery moves. All subskills have been introduced, practiced, and retrieved before the boss.

---

## 7. Learner Simulation

### Attentive novice

**First likely stuck point**: L03 (Pair construction). The `refine <(0, 1), ?_>` syntax with nested angle brackets is unfamiliar. The hint gives it explicitly, so the stuck point is resolvable.

**Most likely wrong move (per level)**:
- L01: Trying `decide` (blocked). The hint says `intro i` immediately.
- L03: Trying `use (0, 1)` instead of `refine`. Works but unhinted. Not a real problem.
- L04: Trying `cases a` instead of `fin_cases a`. Produces harder goals. No rescue hint for this wrong move. The introduction says to use `fin_cases`.
- L06: Trying `contradiction` after `intro h`. Does not work. No rescue hint.
- L11: May struggle to find the correct preimages for the swap (different from cyclic shift). Hints provide them.

**Critical wrong move**: Typing `trivial` on any level. **Now correctly blocked.** The player gets an error message indicating the tactic is disabled.

**Lesson legibility**: Each level's intro clearly states the lesson. Conclusions reinforce with summaries and plain-language translations.

### Experienced Lean user

**Avoidable friction**: L01 and L02 are easy warm-ups. L10 is also simple. All appropriate for their positions in the ladder.

**Expert exploit risk**:
- `norm_num [Fin.forall_fin_succ]` closes L01, L02 (requires knowing a specific Mathlib lemma). P2.
- `rfl` closes L08 (unavoidable definitional reduction). P2.
- No other expert exploits found.

**Alias gaps**:
- L03: `use` works as alternative to `refine`. No Branch or hint covers it.
- L07: `exact absurd (h rfl) (by ...)` or similar may work.

**Inventory clutter**: The world adds 12 items total (3 tactics, 4 definitions, 3 theorems, 2 hidden tactics). Each is documented. Manageable.

---

## 8. Boss Integrity (L11)

### Seeded subskills: All seeded (see 6c above).

### Closure quality: Every boss move has been introduced, practiced, and retrieved before the boss. The specific preimage assignments differ (swap vs cyclic shift), forcing genuine thought.

### Integration quality: The boss uses a **different function** (swap: `0->0, 1->2, 2->1`) than the training function (cyclic shift: `0->1, 1->2, 2->0`). The learner must determine different contradiction/equality patterns and find different preimages. This is genuine integration.

### Gauntlet check: L11 is NOT a gauntlet because it uses a different function than L09. The learner cannot copy-paste from L09.

### Surprise burden: None. Every tactic and proof pattern in the boss was used in L04-L09. Proof length comparable to L09.

### Can the learner explain why? Yes. "The swap sends 0 to 0, 1 to 2, and 2 to 1. It is injective because the three outputs are distinct. It is surjective because every element has a preimage."

---

## 9. Course-Role Sanity

**Intended role**: Example / case-study world.
**Actual role**: Example / case-study world. **Correctly cast.**

Evidence:
- Grounds abstract theory (`Fin n`, injectivity, surjectivity, bijectivity) in concrete computation on `Fin 3`
- Requires the learner to DO the concrete computation (no automation bypass after `trivial` fix)
- Builds intuition through hands-on case-by-case engagement
- Retrieves `fin_cases` from prior world on new ground (fresh surface)
- Views the same object (`Fin 3`) through multiple lenses
- Includes counterexample thinking (L06, L07)
- Has strong transfer language throughout
- L10 adds genuine mathematical insight (involution, function order) previewing group theory

---

## 10. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| Missing `TacticDoc trivial` | P2 | Build info warning: `Missing Tactic Documentation. Using existing docstring. Add trivial`. Player sees fallback docstring. Not blocking. |
| L04/L09/L11 compound `<;>` closer | P1 | Reference proofs use compound tactic. Hints describe step-by-step. Carried from R2/R3. |
| `rfl` closes L08 | P2 | Definitional reduction unavoidable. Hints guide learner to intended method. |
| `norm_num [Fin.forall_fin_succ]` closes L01, L02 | P2 | Expert-only exploit requiring untaught library lemma. Novice unreachable. |
| `Fintype.card` introduced 7 levels early | P3 | NewDefinition in L01, first used in L08. Minor inventory clutter. |
| No `Branch` for `use` vs `refine` in L03 | P2 | `use (0, 1)` works but unhinted. |
| No rescue hint for `cases` vs `fin_cases` | P2 | Novice may try `cases i` producing harder goals. |
| L06 `by omega` subproof compatibility | No risk | `omega` is not in L06's `DisabledTactic`. The `by omega` inside `obtain` compiles correctly. |

---

## 11. Ranked Patch List

### P0 (blocking -- must fix)

None.

### P1 (high -- should fix)

1. **Make L04's reference proof step-by-step** (carried from R2/R3). Replace the compound closer with explicit case blocks so the game's proof panel shows the incremental approach. Move the compound version to a hidden hint as an optimization the learner can discover later.

2. **Add `TacticDoc trivial`** to eliminate the build warning. Place it in L01 (or a metadata file) before the `DisabledTactic` line. Suggested doc:
   ```
   /-- `trivial` attempts to close a goal using simple methods including
   `assumption`, `rfl`, and `Decidable` evaluation. On small finite types,
   it can solve goals automatically without showing any proof steps.

   In this course, `trivial` is disabled so that you practice the manual
   proof patterns. -/
   TacticDoc trivial
   ```

### P2 (medium -- nice to fix)

3. **Add a `Branch` in L03 for `use (0, 1)`** as an alternative to `refine <(0, 1), ?_>`.

4. **Add a rescue hint for `cases` vs `fin_cases`** in levels that use `fin_cases` (especially L01, L04).

5. **Move `NewDefinition Fintype.card` from L01 to L08** where it is first used, to reduce inventory clutter.

6. **Consider adding `omega` to `DisabledTactic` on L03-L09 for consistency**, since `omega` is already disabled on L01, L02, L10, L11. Exception: L06 should keep `omega` enabled for the `by omega` subproof. Verify L06 compatibility before changing.

### P3 (low -- optional)

7. **Add `Branch` in L04/L09/L11 for the step-by-step proof path** alongside the compound version.

---

## 12. What to Playtest Again After Patching

If P1 patches are applied:
1. Verify L04 compiles with the new step-by-step reference proof.
2. Verify `TacticDoc trivial` is accepted and the build info warning disappears.
3. Verify all 11 levels still compile.

No further full re-audit is needed. The world is structurally sound. The P1/P2 patches are localized improvements that do not affect the world's overall quality.

---

## 13. Summary of Defect Counts

| Severity | Count | R3 comparison |
|----------|-------|---------------|
| P0 (blocking) | 0 | Down from 1 (trivial fixed) |
| P1 (high) | 2 (L04 compound proof; missing TacticDoc trivial) | Same type, refined |
| P2 (medium) | 4 (Branch/use, rescue/cases, Fintype.card placement, omega consistency) | Stable |
| P3 (low) | 1 (Branch for L04 step-by-step) | Reduced |
| **Total** | **7** | **Down from 7 (but P0 count: 0 vs 1)** |

---

## 14. Comparison Across Rounds

| Dimension | R1 | R2 | R3 | R4 |
|-----------|----|----|-----|-----|
| Levels | 6 | 10 | 11 | 11 |
| Boss | None | L10 (swap) | L11 (swap, renumbered) | L11 (same) |
| DisabledTactic coverage | 0/6 levels | 10/10 levels | 11/11 levels (missing trivial) | 11/11 levels (trivial included) |
| Exploitable levels (P0) | 5/6 (decide) | 2/10 (omega) | 11/11 (trivial) | **0/11** |
| Exploitable levels (P2) | N/A | N/A | N/A | 3/11 (expert-only: L01, L02, L08) |
| Rubric average | 1.3 | 3.4 | 3.1 | **3.4** |
| Rubric minimum | 0 | 3 | 2 | **3** |
| Overall verdict | FAIL | CONDITIONAL PASS | FAIL | **PASS** |

The `trivial` fix resolves the R3 blocking defect. The world now meets the quality bar for the first time: average >= 3, minimum >= 3, no P0 defects, no automatic red flags.

---

## 15. Final Assessment

The FinThreeExamples world (W3_ex) is a well-constructed example/case-study world that successfully concretizes abstract finite type concepts (`Fin n`, injectivity, surjectivity, bijectivity, involution) by grounding them in exhaustive computation on `Fin 3`. The 11-level progression moves naturally from warm-up through property verification, counterexample thinking, counting, integration, enrichment, and boss. Transfer language is strong throughout.

After four rounds of auditing, the exploit surface is clean:
- All high-risk automation tactics (trivial, decide, native_decide, simp, simp_all, aesop) are disabled on all 11 levels.
- `omega` and `norm_num` are disabled on levels where they would bypass the intended proof.
- Remaining exploit vectors (expert `norm_num` with library lemmas, `rfl` on L08) require either untaught knowledge or are inherent to the statement type, and are classified P2.

The world is ready for integration into the course.
