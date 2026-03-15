# Playtest Audit R1: W3_ex (FinThreeExamples)

**Auditor**: playtest-auditor
**Date**: 2026-03-14
**World files**: `Game/Levels/FinThreeExamples/L01_Enumerate.lean` through `L06_Transfer.lean`
**Build status**: Compiles (verified)
**Predecessor worlds**: FinIntro (13 levels), FinCompute (11 levels)
**World role**: Example / case-study world for `Fin 3`

---

## 1. Overall Verdict

**FAIL -- requires significant rework.**

This world has severe structural problems. Every level except L06 is closable by a single automation tactic (`decide`, `norm_num`, or `exact default`) with no gating. The world introduces at least three new mathematical concepts (`Fintype.card`, `Function.Injective`, `Function.Surjective`) without any inventory declarations, documentation, or `NewDefinition`/`NewTheorem` entries. There is no boss level. The "transfer" level (L06) is actually about `Fin 0`, not `Fin 3`, creating narrative drift. The world has zero `DisabledTactic` declarations anywhere, making every decidable statement trivially closable.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 1 | Three new definitions used but never declared or documented. No closure at all. |
| 2. Granularity fit | 2 | Levels are individually well-scoped but collectively the world skims -- six levels for what should be a rich example world is thin. No practice, no retrieval, no boss. |
| 3. Proof-move teaching | 1 | No proof moves are taught. Five of six levels use single-tactic automation. L06 uses `intro` + `exact` on a familiar pattern. |
| 4. Inventory design | 0 | Zero `NewTactic`, `NewTheorem`, `NewDefinition`, `TacticDoc`, `TheoremDoc`, or `DefinitionDoc` entries in the entire world. `Fintype.card`, `Function.Injective`, `Function.Surjective` appear without documentation. |
| 5. Hint design and recoverability | 1 | Every hint is a spoiler that gives the exact tactic. No layered hints. No strategy hints. No rescue for wrong moves. |
| 6. Progression (worked example -> practice -> boss) | 1 | No boss. No practice levels. No retrieval. Six one-shot introductions with no follow-up. |
| 7. Mathematical authenticity | 2 | The mathematical ideas (counting, function evaluation, products, injectivity, non-surjectivity) are sound and well-chosen. The intros and conclusions are well-written with good transfer language. But the levels themselves demand nothing from the learner. |
| 8. Paper-proof transfer | 2 | The conclusions do translate proofs to plain language. But the learner never actually does a multi-step proof to internalize the transfer. |
| 9. Technical fit and maintainability | 2 | Compiles. But missing all inventory DSL, no documentation, no tactic gating. |

**Average**: 1.3
**Minimum**: 0 (Inventory design)

Verdict: Does not meet the minimum bar (average >= 3, no category below 2).

---

## 3. Coverage Gaps

### 3a. Missing inventory declarations (P0 -- blocking)

The following items are used in the world but have NO `NewDefinition`, `NewTheorem`, `DefinitionDoc`, or `TheoremDoc` entries anywhere in the course:

| Item | Used in | Type needed |
|------|---------|-------------|
| `Fintype.card` | L01 | `NewDefinition` + `DefinitionDoc` |
| `Function.Injective` | L04 | `NewDefinition` + `DefinitionDoc` |
| `Function.Surjective` | L05 | `NewDefinition` + `DefinitionDoc` |
| `Fin.castSucc` composition | L04 | Already has doc from FinIntro, but the composition pattern is new |
| `Prod` (product type `Fin 3 x Fin 3`) | L03 | `NewDefinition` + `DefinitionDoc` |

A learner encountering `Function.Injective` for the first time in L04 has no definition to read, no doc panel entry, and no explanation of what the goal means beyond the intro text.

### 3b. Proof-move coverage (P0 -- blocking)

The plan says this world should exercise proof move V2 (exhaustion on `Fin n`) and provide retrieval for N9 (`fun i : Fin n => ...`). Instead:

| Planned coverage | Actual coverage |
|-----------------|-----------------|
| V2 (R) -- retrieval of exhaustion | Not present. `decide`/`norm_num` close everything without `fin_cases`. |
| N9 (R) -- retrieval of function notation | L02 uses lambda in the statement but the learner never writes one. |
| E1 (I,S) -- concretization of Fin | Partially present but passive (learner types `decide`, not reasoning). |
| M14 (preview) -- product types | L03 is a preview, but the learner types `exact (2, 1)` -- no engagement with the product structure. |

### 3c. Example-axis coverage

For an example world, this is remarkably thin on concrete engagement. The learner never:
- Enumerates elements by hand (e.g., using `fin_cases`)
- Writes a function on `Fin 3` by cases
- Checks injectivity by case-splitting manually
- Derives the surjectivity failure by exhibiting the missing element

Every concrete task is delegated to automation.

---

## 4. Granularity Defects

### 4a. No boss (P0 -- blocking)

The plan specifies 6 levels for W3_ex. Level 6 is labeled "Transfer" but it is NOT a boss. A 6-level example world with no integrating boss means the learner never combines the skills. The plan does not explicitly list a boss for this world, but the quality rubric requires one for any world that teaches reusable content.

### 4b. World is too thin (P1 -- high)

Six levels for an example world that is supposed to concretize `Fin 3` thoroughly is not enough when:
- There is no practice on any introduced concept
- There is no retrieval of prior skills
- There is no boss

The plan says the world promise is "The learner has concretized `Fin` by exhaustively working with `Fin 3` as the set `{0, 1, 2}`." But the learner does not work *exhaustively* with anything -- `decide` does the exhaustion for them.

### 4c. L06 is misclassified (P1 -- high)

L06 ("Transfer: Fin 3 in plain language") proves `forall i : Fin 0, False`. This is:
1. Not about `Fin 3` -- it is about `Fin 0`
2. Not a transfer level -- it is a rehash of FinIntro L05 (which already proved exactly this pattern with `Fin.elim0`)
3. The conclusion summarizes all 6 levels in plain language, which is good transfer content, but the *level itself* is redundant with FinIntro

---

## 5. Statement Exploitability (P0 -- blocking)

### Level-by-level exploitability analysis

| Level | Statement | Exploit | Severity |
|-------|-----------|---------|----------|
| L01 | `Fintype.card (Fin 3) = 3` | `decide`, `native_decide`, `simp [Fintype.card_fin]`, `norm_num [Fintype.card_fin]` | **P0**: `decide` IS the intended proof. Level teaches nothing -- it is pure button-pushing. |
| L02 | `(fun i : Fin 3 => ...) 0 + ... = 8` | `norm_num` (intended), `decide`, `native_decide` | **P0**: `norm_num` is the intended proof. No gating of `decide`. Level teaches no proof move. |
| L03 | `Fin 3 x Fin 3` (type inhabitation) | `exact (0, 0)`, `exact default`, `decide` | **P0**: Unconstrained return type. ANY pair works. `exact default` works. The specific pair `(2, 1)` is not required by the type. |
| L04 | `Function.Injective (Fin.castSucc . Fin.castSucc : Fin 3 -> Fin 5)` | `decide` (intended) | **P0**: `decide` IS the intended proof. No manual engagement with injectivity. |
| L05 | `not Function.Surjective (Fin.castSucc : Fin 3 -> Fin 4)` | `decide` (intended) | **P0**: `decide` IS the intended proof. No manual engagement with surjectivity or the witness `3`. |
| L06 | `forall i : Fin 0, False` | `intro i; exact i.elim0` (intended), `exact Fin.elim0` (one-liner), `intro i; exact absurd i.isLt (by omega)` | **P1**: Multiple paths, but the level at least requires thinking about `Fin 0` emptiness. However, it duplicates FinIntro L05. |

**Summary**: 5 of 6 levels are exploitable with zero engagement. The world's proofs are one-tactic automation shots. This fundamentally defeats the purpose of an example/case-study world. The learner types one word and moves on. Nothing is learned.

---

## 6. Interactive Proof Quality

| Level | Steps | Interactive quality |
|-------|-------|-------------------|
| L01 | 1 (`decide`) | No interaction. One step, done. |
| L02 | 1 (`norm_num`) | No interaction. One step, done. |
| L03 | 1 (`exact (2, 1)`) | No interaction. One step, done. |
| L04 | 1 (`decide`) | No interaction. One step, done. |
| L05 | 1 (`decide`) | No interaction. One step, done. |
| L06 | 2 (`intro i`, `exact i.elim0`) | Minimal interaction. The two-step structure is fine but trivial. |

An example world should have richer interaction. The learner should be exploring, computing, case-splitting, and assembling. Instead, every level is "type one tactic, done."

---

## 7. Hint Design

Every hint in this world is a direct spoiler:

| Level | Hint | Issue |
|-------|------|-------|
| L01 | "Try `decide`." | Spoiler. No strategy layer. |
| L02 | "Try `norm_num`." | Spoiler. No strategy layer. |
| L03 | "Use `exact (2, 1)`." | Spoiler. Gives the exact term. |
| L04 | "`decide` can check all pairs." | Spoiler. Tells the answer directly. |
| L05 | "`decide` checks whether every element has a preimage." | Spoiler. |
| L06a | "Introduce `i : Fin 0` with `intro i`." | Acceptable first hint. |
| L06b | "Use `exact i.elim0`." | Spoiler for second step. Should be hidden. |

No level has layered hints (strategy visible, code hidden). No level has hints for wrong moves. No level has `Branch` handling for alternative approaches.

---

## 8. Learner Simulation

### Attentive novice

**First likely stuck point**: L03 (Pairing elements). The goal is `Fin 3 x Fin 3` with no hypotheses. A novice may not know they can type `exact (2, 1)`. However, the hint gives it away immediately.

**Most likely wrong move**: In L06, trying `cases i` instead of `exact i.elim0`. No rescue hint exists for this.

**Does the novice learn?**: No. The novice reads the introduction (which is well-written and informative), types one tactic, reads the conclusion (also well-written). The learning happens through reading, not through proving. The world is a textbook chapter with interactive checkboxes, not an interactive proof experience.

**Legibility of lessons**: The introduction text clearly explains each concept. But the *level's lesson* (what the learner practices by doing the proof) is always "type `decide`" or "type `norm_num`". The mathematical lesson and the proof lesson are decoupled.

### Experienced Lean user

**Avoidable friction**: The experienced user will type `decide` for everything and finish the world in under 2 minutes. They will learn nothing.

**Alias gaps**: None relevant -- the world uses so few tactics that aliases are not a concern.

**Inventory clutter**: The world adds zero inventory items (which is worse than clutter -- it is absence).

**Needless forced verbosity**: None. If anything, the world is too terse in what it demands.

---

## 9. Course-Role Sanity

**Intended role**: Example / case-study world.

**Actual role**: Trivial computation verification world.

An example world should:
- Ground abstract theory in concrete computation
- Require the learner to DO the concrete computation (not delegate to `decide`)
- Build intuition through hands-on engagement
- Revisit prior proof moves on concrete ground
- Possibly introduce "the same object through a different theoretical lens"

This world fails on all counts except narrative framing. The introductions and conclusions describe the concrete engagement well, but the levels themselves do not deliver it.

**Specific mismatch**: L04 and L05 introduce `Function.Injective` and `Function.Surjective` -- these are NEW abstract definitions, not concrete exercises with existing theory. An example world should exercise existing theory on concrete ground, not introduce new abstractions. The plan marks these as "V2 (R)" (retrieval of exhaustion) and "V9 (preview)" (pigeonhole preview), which is reasonable in principle, but the actual levels use `decide` instead of exhaustion, defeating the retrieval purpose.

---

## 10. Boss / Integration Assessment

**No boss exists.** This is a blocking defect for any world with 6 levels.

A proper boss for this world should integrate:
- Counting elements (Fintype.card)
- Computing function values on `Fin 3`
- Reasoning about pairs
- Case-splitting on `Fin 3` elements
- Combining at least 3 proof moves in one proof

---

## 11. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| Zero inventory declarations | P0 | No `NewTactic`, `NewTheorem`, `NewDefinition`, `TacticDoc`, `TheoremDoc`, or `DefinitionDoc` in the entire world. Learner's inventory panel gets nothing. |
| No `DisabledTactic` anywhere | P0 | `decide` and `native_decide` are available and close 5 of 6 levels trivially. Previous world (FinCompute) explicitly gated these in many levels. |
| L03 unconstrained return type | P0 | Goal `Fin 3 x Fin 3` accepts any pair, including `default`. The specific pair `(2, 1)` is not enforced by the type system. |
| L06 duplicates FinIntro L05 | P1 | FinIntro L05 already teaches `Fin 0 -> False` with `Fin.elim0`. L06 repeats this without adding value. |
| No `Branch` for alternative proofs | P2 | L04 and L05 could be solved manually (intro + fin_cases) but no Branch exists for this path. |

---

## 12. Ranked Patch List

### P0 (blocking -- must fix before shipping)

1. **Redesign ALL proofs to require manual engagement.** For an example world, the learner must DO the concrete work, not type `decide`. Specific redesigns:
   - **L01**: Disable `decide`/`native_decide`. Require `simp [Fintype.card_fin]` or even better, restructure the statement to require the learner to show that `Finset.univ` for `Fin 3` has specific elements.
   - **L02**: Already uses `norm_num` which is reasonable for arithmetic. But the statement should require the learner to first beta-reduce the lambdas using `simp only [Fin.val]` or `norm_num` step by step, not one shot.
   - **L03**: Fix the unconstrained return type. Instead of `Fin 3 x Fin 3`, require a specific pair: `exists p : Fin 3 x Fin 3, p.1 = 2 and p.2 = 1` or prove an equation like `((2, 1) : Fin 3 x Fin 3).1 = 2`.
   - **L04**: Disable `decide`/`native_decide`. Require manual proof: `intro a b h; fin_cases a <;> fin_cases b <;> simp_all` or similar. This actually exercises the exhaustion proof move (V2 retrieval).
   - **L05**: Disable `decide`/`native_decide`. Require `intro h; obtain <a, ha> := h 3; fin_cases a <;> simp at ha` or similar. This teaches counterexample extraction.

2. **Add inventory declarations for all new items.** At minimum:
   - `NewDefinition Fintype.card` + `DefinitionDoc` in L01
   - `NewDefinition Function.Injective` + `DefinitionDoc` in L04
   - `NewDefinition Function.Surjective` + `DefinitionDoc` in L05
   - Consider `NewDefinition Prod` + `DefinitionDoc` in L03

3. **Add a boss level (L07 or replace L06).** The boss should require the learner to combine counting, function evaluation, case analysis, and injectivity/surjectivity reasoning in a single proof. Example: "Prove that there are exactly 6 injective functions from `Fin 2` to `Fin 3`" or "Prove that the function mapping each `i : Fin 3` to `(i, i)` is injective."

4. **Add `DisabledTactic` declarations.** At minimum, disable `decide` and `native_decide` in L01, L04, and L05 where manual proofs should be required. Consider disabling them world-wide except where explicitly needed.

### P1 (high -- should fix)

5. **Replace L06 with a genuine transfer level about Fin 3.** The current L06 proves `forall i : Fin 0, False`, which duplicates FinIntro L05. A proper transfer level should ask the learner to prove something about `Fin 3` that connects back to everyday math. Options:
   - Prove that every function `Fin 3 -> Fin 3` that is injective is also surjective (a finite pigeonhole preview using `Fintype.card` reasoning)
   - Prove that `Fin 3 x Fin 3` has exactly 9 elements
   - The conclusion should connect back to paper proofs

6. **Add practice levels.** The world needs at least 2-3 more levels to provide supported practice before any boss. Candidates:
   - A second injectivity proof on a different function (retrieval)
   - A surjectivity proof that SUCCEEDS (to contrast with L05)
   - A level where the learner defines a function on `Fin 3` by cases and proves a property

7. **Redesign hints as layered (strategy first, code hidden).** Every hint should have:
   - Visible: a strategy hint ("Think about what happens when you apply `f` to each element")
   - Hidden: the code template ("Try `fin_cases a <;> fin_cases b <;> simp_all`")

### P2 (medium -- nice to fix)

8. **Add `Branch` alternatives for levels with multiple valid proof paths.** L04 and L05 should support both the manual proof path and (if decide is re-enabled) the automation path with appropriate branches and hints.

9. **Improve the L02 statement.** Instead of writing the lambda three times in the goal, define a local function and use it. The current statement is syntactically noisy.

10. **Add a level that explicitly builds a function on `Fin 3` by cases.** This would retrieve the function-construction skill from FinCompute L08. The learner should write `fun i => match i with | 0 => ... | 1 => ... | 2 => ...` or use `Fin.cons`.

---

## 13. What to Playtest Again After Patching

After implementing patches 1-7, re-audit:

1. **Exploitability**: Verify that `decide`/`native_decide` are properly disabled and that no remaining level is closable by a single automation tactic that bypasses the intended lesson.
2. **Boss integrity**: Verify the new boss integrates at least 3 distinct subskills from the world.
3. **L03 pinning**: Verify the redesigned L03 actually requires the specific pair, not `default` or any arbitrary element.
4. **Inventory panel**: Verify that `Fintype.card`, `Function.Injective`, `Function.Surjective` appear in the learner's inventory panel with documentation.
5. **Hint layering**: Verify that at least L04, L05, and the boss have strategy-first hint chains.
6. **Transfer level**: Verify the replacement L06 is genuinely about `Fin 3` and connects to paper proof language.
7. **Coverage**: Re-run coverage mapper to verify V2 retrieval and E1 concretization are actually delivered.

---

## 14. Summary of Defect Counts

| Severity | Count |
|----------|-------|
| P0 (blocking) | 4 (exploitability, missing inventory, no boss, unconstrained L03) |
| P1 (high) | 3 (L06 mismatch, thin world, spoiler hints) |
| P2 (medium) | 3 (branches, L02 syntax, function construction level) |
| **Total** | **10** |

This world needs a complete rework of its proof layer while preserving its (well-written) narrative layer. The introductions and conclusions are strong -- they explain the mathematics clearly and include transfer language. But the proofs themselves are empty shells. An example world that delegates all concrete work to automation is not an example world.
