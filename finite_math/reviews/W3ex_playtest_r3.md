# Playtest Audit R3: W3_ex (FinThreeExamples)

**Auditor**: playtest-auditor
**Date**: 2026-03-15
**Round**: 3 (re-audit after R2 conditional-pass fixes + new level)
**World files**: `Game/Levels/FinThreeExamples/L01_Enumerate.lean` through `L11_Boss.lean` (11 levels)
**Build status**: Compiles (`lake build` succeeds, 8125 jobs)
**Predecessor worlds**: FinIntro (12 levels), FinCompute (11 levels)
**World role**: Example / case-study world for `Fin 3`

---

## 1. Overall Verdict

**FAIL -- one P0 defect (all 11 levels exploitable by `trivial`).**

The R2 P0 defect (`omega` exploiting L01/L02) has been fixed: `omega` is now in the `DisabledTactic` list for L01 and L02. The new L10 (Involution) is well-constructed and fits cleanly into the level ladder. The boss (now L11) compiles and is correctly renumbered.

However, a critical new finding: **`trivial` closes every single level (all 11) in a single tactic call, and `trivial` is not disabled on any level.** This is a P0 blocking defect that must be fixed before the world can pass. The fix requires adding a `TacticDoc trivial` entry and then adding `trivial` to `DisabledTactic` on all 11 levels.

### R2 defect resolution status

| R2 defect | Severity | Status | Evidence |
|-----------|----------|--------|----------|
| `omega` exploits L01 and L02 | P0 | **FIXED** | `DisabledTactic` on L01: `decide native_decide omega simp aesop simp_all`. L02: same. `omega` now correctly blocked. |
| L04 compound one-liner reference proof | P1 | **NOT FIXED** | L04 reference proof is still `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)`. The hints describe the step-by-step path, which partially mitigates this. Carried forward as P1. |

### Changes since R2

| Change | Assessment |
|--------|-----------|
| `omega` added to `DisabledTactic` in L01, L02 | Correct and effective. |
| New L10_Involution.lean added | Well-designed level. Proves the swap is an involution (`f(f(i)) = i`). Clean proof: `intro i; fin_cases i <;> rfl`. Good pedagogical content distinguishing involutions from non-involutions (order 2 vs order 3). |
| Boss renumbered from L10 to L11 | Correct. `Level 11` in the file. World base file imports all 11 levels. |
| L04 pattern naming in conclusion | Minor improvement -- the "Fin.val extraction move" is now named explicitly. |
| L09 repetition acknowledgment | Minor improvement -- the intro now acknowledges re-proving injectivity/surjectivity as deliberate practice. |
| L11 boss permutation table in conclusion | Good addition -- lists all 6 permutations of `Fin 3` with their orders, connecting the world's two worked functions (cyclic shift and swap) to the complete picture. |

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | All items have proper declarations, but the `trivial` exploit means NO level actually tests the intended coverage. A learner can type `trivial` on every level and learn nothing. Score capped at 2 until `trivial` is disabled. |
| 2. Granularity fit | 4 | 11 levels with clear progression. L10 (Involution) is a welcome addition that adds a genuinely new concept (function composition, order) without introducing new proof moves. No level is too broad or too fine. |
| 3. Proof-move teaching | 2 | The intended proof moves are well-designed, but `trivial` bypasses all of them. Score capped at 2. |
| 4. Inventory design | 3 | All new items documented. New `TacticDoc` for `left`, `right`, `obtain`. New `DefinitionDoc` for `Function.Injective`, `Function.Surjective`, `Function.Bijective`, `Fintype.card`. New `TheoremDoc` for `Fin.val_castSucc`, `Fintype.card_prod`, `Fintype.card_fin`. `TheoremTab` used. Score not affected by `trivial` since inventory itself is correct. |
| 5. Hint design and recoverability | 3 | Layered hints throughout. Strategy hints visible, code hints hidden. Each `fin_cases` branch has its own hint. Deducted 1 for no `Branch` alternatives (e.g., `use` vs `refine` in L03, `cases` vs `fin_cases`). |
| 6. Progression (worked example -> practice -> boss) | 4 | Excellent arc: L01-L02 (warm-up), L03 (construction), L04-L05 (positive properties), L06-L07 (counterexamples), L08 (counting), L09 (integration), L10 (new concept), L11 (boss on different function). Support is faded well. L10 adds a fresh concept before the boss without increasing boss difficulty. |
| 7. Mathematical authenticity | 4 | Rich concretization. The dual pair L06/L07 (pigeonhole preview) is pedagogically strong. L10's involution concept with the comparison table (order 2 vs 3) is genuine mathematical content. Transfer language in every conclusion. |
| 8. Paper-proof transfer | 4 | Every conclusion includes plain-language translation. The L11 boss conclusion has a comprehensive skills table and plain-language summaries for all 11 levels (updated to include L10). The permutation table in L11 connects concrete examples to the broader mathematical picture. |
| 9. Technical fit and maintainability | 2 | Compiles cleanly. Dependencies correct. World base file updated with L10 and L11. Score capped at 2 due to `trivial` exploit undermining the entire world. |

**Average**: 3.1 (dragged down by `trivial` exploit)
**Minimum**: 2 (three categories: coverage, proof-move, technical)

**Verdict**: Does NOT meet the minimum bar (categories below 2 are not present, but the 2s are only due to `trivial` -- fixing `trivial` would immediately raise them to 3+). After the `trivial` fix, scores would be approximately: coverage 3, proof-move 3, technical 3, average 3.4, minimum 3.

---

## 3. Coverage Gaps

### 3a. Critical exploit: `trivial`

| Level | Exploitable by `trivial`? | Verified |
|-------|--------------------------|----------|
| L01 | **YES** | `example : forall i : Fin 3, i = 0 or i = 1 or i = 2 := by trivial` compiles |
| L02 | **YES** | `example : forall i : Fin 3, (2 * i.val + 1) % 2 = 1 := by trivial` compiles |
| L03 | **YES** | `example : exists p : Fin 3 x Fin 3, p.1 != p.2 := by trivial` compiles |
| L04 | **YES** | `example : Function.Injective (fun i : Fin 3 => match i with | 0 => (1 : Fin 3) | 1 => 2 | 2 => 0) := by trivial` compiles |
| L05 | **YES** | Verified: `trivial` closes the surjectivity statement |
| L06 | **YES** | Verified: `trivial` closes the negated surjectivity statement |
| L07 | **YES** | Verified: `trivial` closes the negated injectivity statement |
| L08 | **YES** | Verified: `trivial` closes the cardinality statement |
| L09 | **YES** | Verified: `trivial` closes the bijectivity statement |
| L10 | **YES** | Verified: `trivial` closes the involution statement |
| L11 | **YES** | Verified: `trivial` closes the boss statement |

**11 of 11 levels are exploitable by `trivial`.** This is a single-tactic bypass that requires zero engagement with the intended lesson.

**Root cause**: `trivial` in Lean 4/Mathlib dispatches to `Decidable` reduction. All statements in this world are decidable over small `Fin n` types, so `trivial` can evaluate them directly. The tactic is not in any `DisabledTactic` list, and no `TacticDoc trivial` exists to enable disabling it.

**Fix**: Two steps are required:
1. Add `TacticDoc trivial` (required by `checkInventoryDoc` before `DisabledTactic` can reference it). This can be placed in any level file -- ideally in a shared metadata file or in L01.
2. Add `trivial` to `DisabledTactic` on all 11 levels.

**Implementation note**: The `TacticDoc` must appear BEFORE any `DisabledTactic trivial` in file processing order. Place the `TacticDoc` in L01 (the first level processed) or in a metadata file.

### 3b. R2 omega fix verification

`omega` is now correctly disabled on L01 and L02:
- L01: `DisabledTactic decide native_decide omega simp aesop simp_all`
- L02: `DisabledTactic decide native_decide omega simp aesop simp_all`

`omega` is NOT disabled on L03-L09, L11. This is acceptable because `omega` cannot close any of these levels' top-level goals (verified: `omega` fails on Function.Injective, Function.Surjective, etc.). L10 also disables `omega` for consistency.

`omega` is used inside `by omega` in L06's `obtain <a, ha> := h <3, by omega>`. Since `omega` is not in L06's `DisabledTactic` list, this works. If `omega` were added to L06's list for consistency, the `by omega` subproof context might still work (game server may not enforce `DisabledTactic` inside `by` subproofs), but this has not been tested and is not necessary since `omega` cannot close L06's top-level goal.

### 3c. Other exploit vectors checked

| Tactic | Can close any level? | Disabled? |
|--------|---------------------|-----------|
| `decide` | Yes (most levels) | Yes (all 11 levels) |
| `native_decide` | Yes (most levels) | Yes (all 11 levels) |
| `omega` | L01, L02 only | Yes (L01, L02, L10) |
| `simp` | Yes (many levels) | Yes (all 11 levels) |
| `simp_all` | Yes (many levels) | Yes (all 11 levels) |
| `aesop` | Yes (many levels) | Yes (all 11 levels) |
| `norm_num` | Some levels | Yes (L05, L08, L09) |
| **`trivial`** | **Yes (ALL 11 levels)** | **NOT disabled** |
| `tauto` | No (tested on L01: fails) | Not needed |

### 3d. Coverage closure assessment (assuming `trivial` is fixed)

| Item | Axis | Coverage states | Assessment |
|------|------|-----------------|------------|
| `Fin 3` concretization | EXAMPLE | I (L01), S (L02-L09), G (L10, L11) | Strong |
| `fin_cases` retrieval | MOVE/LEAN | R (L01-L07, L10), G (L09, L11) | Strong |
| Disjunction navigation (`left`/`right`) | MOVE/LEAN | I (L01) only | Weak closure but acceptable for example world |
| `congr_arg Fin.val h` contradiction pattern | MOVE | I (L03), S (L04), R (L07), G (L11) | Strong |
| `Function.Injective` | MATH | I (L04), R (L09), G (L11) | Adequate |
| `Function.Surjective` | MATH | I (L05), counterexample (L06), R (L09), G (L11) | Strong |
| `Function.Bijective` | MATH | I (L09) | Adequate (not separately used in L11 which uses the explicit conjunction) |
| Function composition / involution | MATH | I (L10) | Introduced, not retrieved in this world (appropriate for example world) |
| `obtain` for existential destruction | LEAN | I (L06) | Introduced; retrieval expected in later worlds |
| `Fintype.card_prod`, `Fintype.card_fin` | MATH/LEAN | I (L08) | Preview for later counting worlds |
| Pigeonhole preview | TRANSFER | L06 (surj fails), L07 (inj fails) | Good narrative setup |

---

## 4. Granularity Defects

### 4a. Level-by-level assessment

| Level | Dominant lesson | One-sentence test | Verdict |
|-------|----------------|-------------------|---------|
| L01 | Exhaustive enumeration + disjunction | "Enumerate Fin 3 via fin_cases + left/right" | Pass (if trivial blocked) |
| L02 | Function evaluation by cases | "Verify a property case-by-case" | Pass (if trivial blocked) |
| L03 | Existential witness with constraint | "Construct a pair and prove inequality" | Pass |
| L04 | Injectivity by double exhaustion | "Check all 9 input pairs for collisions" | Pass |
| L05 | Surjectivity by preimage finding | "Provide a preimage for each output" | Pass |
| L06 | Surjectivity disproof | "Extract and refute a preimage for a missed element" | Pass |
| L07 | Injectivity disproof | "Find a collision and derive contradiction" | Pass |
| L08 | Cardinality of product types | "Count via card_prod and card_fin rewrites" | Pass |
| L09 | Bijectivity = inj + surj | "Combine L04 and L05 patterns via constructor" | Pass |
| L10 | Involution verification | "Show f(f(i)) = i by case analysis" | Pass |
| L11 | Boss: integration on new function | "Prove inj+surj for the swap permutation" | Pass |

### 4b. L10 (new level) detailed assessment

**Dominant lesson**: Function composition and the involution property. The proof is simple (`intro i; fin_cases i <;> rfl`), which is appropriate because the NEW concept is the mathematical idea (applying a function twice), not a new proof technique.

**Novelty budget**: The only new burden is the mathematical concept of involution/function composition. No new tactics, no new proof patterns. The proof shape (`fin_cases <;> rfl`) was already used in FinCompute. Budget: **within limits**.

**Position in ladder**: Between L09 (bijectivity integration) and L11 (boss). This placement works well -- it introduces a fresh mathematical concept that enriches the world without affecting the boss's requirements. The boss does NOT require the involution concept, so L10 is enrichment, not prerequisite.

**Disabled tactics**: `DisabledTactic decide native_decide simp aesop simp_all omega norm_num`. This is the most restrictive disable list in the world (adding both `omega` and `norm_num`). Since the proof is just `fin_cases <;> rfl`, none of these are needed. Good.

**Pedagogical value**: The comparison table in the conclusion (swap = order 2, cyclic shift = order 3) is genuine mathematical insight that previews group theory concepts. This is exactly what an example world should do.

### 4c. World coherence

The world has a coherent center of gravity: **concrete reasoning about functions on `Fin 3` via exhaustive case analysis**. The 11-level progression is:

1. L01-L02: Warm-up (retrieving `fin_cases` on concrete tasks)
2. L03: Construction (existential witness with constraint)
3. L04-L05: Positive function properties (injectivity, surjectivity)
4. L06-L07: Negative function properties (counterexample thinking)
5. L08: Counting (cardinality of products)
6. L09: Integration (bijectivity = inj + surj)
7. L10: Enrichment (involution -- new concept, familiar proof shape)
8. L11: Boss (same skills, different function)

No splitting needed. The world covers one coherent theme with steady escalation. L10 fits naturally as "one more interesting property of a function on Fin 3" before the boss.

---

## 5. Statement Exploitability (detailed)

See Section 3a for the comprehensive `trivial` exploit table.

**Summary**: All 11 levels are exploitable by `trivial`. After fixing `trivial`, the residual exploit surface is clean: `decide`, `native_decide`, `simp`, `aesop`, `simp_all` are all disabled on every level. `omega` is disabled where it matters (L01, L02, L10). `norm_num` is disabled where it would bypass the intended proof (L05, L08, L09). `tauto` does not close any statement (verified on L01).

---

## 6. Interactive Proof Quality

| Level | Intended proof steps | Interactive? | Notes |
|-------|---------------------|-------------|-------|
| L01 | `intro i` -> `fin_cases i` -> 3x (`left`/`right` + `rfl`) | Yes | Each step gives visible feedback |
| L02 | `intro i` -> `fin_cases i` -> 3x `norm_num` | Yes | Clear step-by-step |
| L03 | `refine <(0,1), ?_>` -> `intro h` -> `have hv` -> `norm_num at hv` | Yes | Four distinct steps |
| L04 | `intro a b h` -> compound closer | **P1** | Reference proof is compound `<;>` one-liner. Hints describe step-by-step. **Carried from R2.** |
| L05 | `intro b` -> `fin_cases b` -> 3x `exact <_, rfl>` | Yes | Clean |
| L06 | `intro h` -> `obtain` -> compound closer | Acceptable | `obtain` expression is complex but hint gives exact syntax |
| L07 | `intro h` -> `have h03` -> `have :=` -> `norm_num at this` | Yes | Excellent interactive flow |
| L08 | `rw [card_prod]` -> `rw [card_fin]` | Yes | Two clean rewrites |
| L09 | `constructor` -> inj block -> surj block | Yes | Integration of L04+L05 |
| L10 | `intro i` -> `fin_cases i` -> 3x `rfl` | Yes | Simplest proof in the world; appropriate for the concept-focused level |
| L11 | `constructor` -> inj block -> surj block | Yes | Boss uses same interactive structure as L09 |

**L04 P1 (carried forward)**: The reference proof `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)` requires the learner to type a compound expression before getting feedback on individual cases. The hints DO describe the step-by-step approach (doing each of the 9 cases individually), but the reference proof in the file is the compound version. This makes the level appear to expect the one-liner in the proof panel.

**L10 assessment**: The proof `intro i; fin_cases i <;> rfl` could use the `<;>` combinator, but each case is just `rfl`, so there is no issue with the learner typing `rfl` in each case individually after `fin_cases i`. The `<;>` is a convenience, not a pedagogical problem.

---

## 7. Learner Simulation

### Attentive novice

**First likely stuck point**: L03 (Pair construction).

The `refine <(0, 1), ?_>` syntax with nested angle brackets is new. The hint gives it explicitly. If the learner tries `use (0, 1)`, that works but no hint covers it.

**Most likely wrong move (per level)**:
- L01: Trying `decide` (blocked) or `omega` (now blocked). Good.
- L03: Trying `use` instead of `refine`. Works but unhinted.
- L04: Trying `cases a` instead of `fin_cases a`. Produces harder goal structure. No rescue hint.
- L06: Trying `contradiction` after `intro h`. Does not work. No rescue hint.
- L10: None likely. The proof is straightforward (`intro i; fin_cases i <;> rfl`).
- L11: May struggle to find the correct preimages for the swap function (different from the cyclic shift). The hints provide them explicitly.

**Critical wrong move**: Typing `trivial` on any level. **This currently works and bypasses everything.** The learner who discovers `trivial` can skip the entire world with zero learning. This is the defining P0 defect.

**Lesson legibility**: Each level's intro clearly states the lesson. Conclusions reinforce with summaries and plain-language translations. L10's comparison table between the swap and cyclic shift is particularly clear. L11's comprehensive skills table is excellent for consolidation.

### Experienced Lean user

**Avoidable friction**: L01 and L02 are trivial even without exploits (`fin_cases` + closer). The experienced user will find these easy. L10 is also very easy (the proof is `fin_cases <;> rfl`). But these are warm-up/enrichment levels, so ease is appropriate.

**Alias gaps**:
- L03: `use` works as alternative to `refine`. No Branch or hint.
- L07: `exact absurd (h rfl) (by omega)` or similar may work. Not hinted.

**Inventory clutter**: The world adds:
- Tactics: `left`, `right`, `obtain` (new), `first`, `exfalso` (hidden)
- Definitions: `Fintype.card`, `Function.Injective`, `Function.Surjective`, `Function.Bijective`
- Theorems: `Fin.val_castSucc`, `Fintype.card_prod`, `Fintype.card_fin`

This is a lot (12 items) but each is well-documented and used in context. Manageable.

---

## 8. Boss Integrity (L11)

### Seeded subskills check

| Subskill | Where seeded | Boss usage |
|----------|-------------|------------|
| `constructor` to split conjunction | L09 (first contact in this world) | Required as first step |
| `intro a b h; fin_cases a <;> fin_cases b` | L04 (first contact), L09 (retrieval) | Required for injectivity |
| `exfalso; congr_arg Fin.val h; norm_num at this` | L03 (intro), L04 (supported), L07 (retrieval) | Required for off-diagonal cases |
| `rfl` for diagonal cases | L04, L09 | Required for diagonal cases |
| `intro b; fin_cases b; exact <_, rfl>` | L05 (first contact), L09 (retrieval) | Required for surjectivity |

**All subskills seeded and practiced.** No lottery moves.

### Closure quality

Every boss move has been introduced, practiced, and retrieved before the boss. The specific preimage assignments differ (swap vs cyclic shift), which forces the learner to think rather than replay. The boss does NOT use the involution concept from L10 -- this is correct since L10 is enrichment, not skill-building.

### Integration quality

The boss uses a **different function** (swap: `0->0, 1->2, 2->1`) than the training function (cyclic shift: `0->1, 1->2, 2->0`). The learner must:
- Determine which pairs give contradictions vs trivial equalities (different structure from cyclic shift)
- Find different preimages (`0 = f 0`, `1 = f 2`, `2 = f 1`)

This is genuine integration. The planning challenge is modest but real -- the learner must think about the specific function, not just replay mechanics.

### Gauntlet check

The boss IS structurally identical to L09 (bijectivity = constructor + injectivity + surjectivity) but on a **different** function. L09 uses the cyclic shift (same function as L04/L05), so L09 is closer to a gauntlet. L11 is the genuine boss because the function is different. The learner cannot copy-paste from L09.

**Verdict**: Acceptable boss. Not exceptional (no novel integration challenge beyond "same proof shape, different data"), but appropriate for an example world that is primarily about concretization rather than proof-technique mastery.

### Surprise burden

None. Every tactic and proof pattern in the boss was used in L04-L09. The proof length is comparable to L09. No surprise.

### Can the learner explain why?

Yes. "The swap function sends 0 to 0, 1 to 2, and 2 to 1. It is injective because the three outputs 0, 2, 1 are all distinct. It is surjective because every element has a preimage: 0 = f(0), 1 = f(2), 2 = f(1)."

---

## 9. Course-Role Sanity

**Intended role**: Example / case-study world.

**Actual role**: Example / case-study world. **Correctly cast.**

Evidence:
- Grounds abstract theory (`Fin n`, injectivity, surjectivity, bijectivity) in concrete computation on `Fin 3`
- Requires the learner to DO the concrete computation (no automation bypass -- once `trivial` is fixed)
- Builds intuition through hands-on case-by-case engagement
- Retrieves `fin_cases` from prior world on new ground
- Views the same object (`Fin 3`) through multiple lenses (enumeration, function evaluation, pairs, injectivity, surjectivity, counting, bijectivity, involution)
- Includes counterexample thinking (L06, L07)
- Has strong transfer language throughout
- L10 (involution) adds genuine mathematical insight that previews group theory concepts

The addition of L10 strengthens the world's role as an example world by adding a concept (involution, function order) that enriches the learner's view of permutations beyond just "bijective or not."

---

## 10. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| `trivial` exploits all 11 levels | **P0** | See Section 3a. Must add `TacticDoc trivial` + `DisabledTactic trivial` on all levels. |
| L04/L09/L11 compound `<;>` closer | P1 | Reference proofs use compound tactic. Hints describe step-by-step. Carried from R2. |
| No `TacticDoc trivial` exists in the project | P0 (dependency) | `DisabledTactic trivial` requires `TacticDoc trivial` to exist first. Must be created. |
| L06 `by omega` subproof under `DisabledTactic omega` | P2 (potential) | If `omega` is added to L06's `DisabledTactic` for consistency, the `by omega` inside `obtain` may break. Not currently an issue since `omega` is not disabled on L06. |
| No `Branch` for `use` vs `refine` in L03 | P2 | `use (0, 1)` works but is unhinted. |
| No rescue hint for `cases` vs `fin_cases` | P2 | Novice may try `cases i` producing harder goals. |

---

## 11. Ranked Patch List

### P0 (blocking -- must fix)

1. **Disable `trivial` on all 11 levels.**

   Required steps:
   a. Add a `TacticDoc trivial` entry. Suggested placement: L01_Enumerate.lean, before the `DisabledTactic` line. Suggested content:
   ```
   /-- `trivial` attempts to close a goal using simple methods including
   `assumption`, `rfl`, and `Decidable` evaluation. On small finite types,
   it can solve goals automatically without showing any proof steps.

   In this world, `trivial` is disabled so that you practice the manual
   proof patterns. -/
   TacticDoc trivial
   ```

   b. Add `trivial` to the `DisabledTactic` list on every level:
   - L01: `DisabledTactic decide native_decide omega simp aesop simp_all trivial`
   - L02: `DisabledTactic decide native_decide omega simp aesop simp_all trivial`
   - L03: `DisabledTactic decide native_decide simp aesop simp_all trivial`
   - L04: `DisabledTactic decide native_decide simp aesop simp_all trivial`
   - L05: `DisabledTactic decide native_decide simp aesop simp_all norm_num trivial`
   - L06: `DisabledTactic decide native_decide simp aesop simp_all trivial`
   - L07: `DisabledTactic decide native_decide simp aesop simp_all trivial`
   - L08: `DisabledTactic decide native_decide simp aesop simp_all norm_num trivial`
   - L09: `DisabledTactic decide native_decide simp aesop simp_all norm_num trivial`
   - L10: `DisabledTactic decide native_decide simp aesop simp_all omega norm_num trivial`
   - L11: `DisabledTactic decide native_decide simp aesop simp_all trivial`

   c. Verify the build succeeds after the change.

   d. Re-test that `trivial` is now blocked on all 11 levels.

   **IMPORTANT**: Also check whether `trivial` is an exploit in ALL other worlds in the course (FinIntro, FinCompute, ListBasics, MultisetHierarchy). If so, those worlds need the same fix. This is a systemic issue, not specific to W3_ex.

### P1 (high -- should fix)

2. **Make L04's reference proof step-by-step** (carried from R2). Replace the compound `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)` with explicit case blocks. Move the compound version to a hidden hint as an optimization the learner can discover.

### P2 (medium -- nice to fix)

3. **Add a `Branch` in L03 for `use (0, 1)`** as an alternative to `refine <(0, 1), ?_>`.

4. **Add a rescue hint for `cases` vs `fin_cases`** in levels that use `fin_cases` (especially L01, L02, L04).

5. **Add `omega` to `DisabledTactic` on remaining levels (L03-L09, L11) for consistency.** While `omega` cannot close these levels' top-level goals, disabling it consistently prevents any future interaction between `omega` and partially-reduced goals. Exception: L06 may need `omega` left enabled for the `by omega` subproof -- test before changing.

### P3 (low -- optional)

6. **Consider whether `left`/`right` should be `NewTactic`** in L01. These are arguably NNG4-baseline. If already unlocked, remove `NewTactic left right`.

7. **Add `Branch` in L04 for the step-by-step proof path** alongside the compound version.

---

## 12. What to Playtest Again After Patching

After implementing patch 1 (`trivial` disabling):

1. **Verify `trivial` is blocked on all 11 levels.** Test that `trivial` alone fails on every statement.
2. **Verify the build succeeds.** Confirm `TacticDoc trivial` + `DisabledTactic trivial` does not break compilation.
3. **Verify no other single-tactic exploit remains.** Check `ring`, `linarith`, `positivity`, `contradiction`, `assumption` on all levels. (Most of these should fail on the statement types, but worth confirming.)
4. **Verify L06's `by omega` subproof still works** after any `DisabledTactic` changes.
5. **Scan ALL other worlds** (FinIntro, FinCompute, ListBasics, MultisetHierarchy) for `trivial` exploitability. This is likely a systemic issue.

---

## 13. Summary of Defect Counts

| Severity | Count | R2 comparison |
|----------|-------|---------------|
| P0 (blocking) | 1 (`trivial` exploit: all 11 levels) | Changed character: R2 had omega on 2 levels; R3 has trivial on 11 levels |
| P1 (high) | 1 (L04 compound reference proof) | Same as R2 (carried forward) |
| P2 (medium) | 3 (Branch for `use`, rescue for `cases`, omega consistency) | Same as R2 |
| P3 (low) | 2 (left/right NewTactic, Branch for L04) | Reduced from R2 |
| **Total** | **7** | **Down from 8** |

---

## 14. Comparison Across Rounds

| Dimension | R1 | R2 | R3 |
|-----------|----|----|-----|
| Levels | 6 | 10 | 11 |
| Boss | None | L10 (swap) | L11 (swap, renumbered) |
| DisabledTactic coverage | 0/6 levels | 10/10 levels | 11/11 levels |
| Exploitable levels | 5/6 (decide) | 2/10 (omega) | **11/11 (trivial)** |
| Rubric average | 1.3 | 3.4 | 3.1 (dragged by trivial) |
| Rubric minimum | 0 | 3 | 2 (trivial) |

The R2 omega fix was successful. The new L10 (Involution) is well-designed. However, the previously undetected `trivial` exploit -- present since R1 but never caught because it was overshadowed by the `decide` and `omega` exploits -- now surfaces as the dominant defect.

**The world is structurally sound.** The pedagogy, coverage, granularity, hints, and transfer language are all strong. The ONLY blocking issue is the `trivial` tactic bypass, which is a surgical fix (add `TacticDoc` + add to `DisabledTactic` lists). After that fix, this world should pass.

---

## 15. L10 (Involution) Specific Assessment

Since L10 is new, a detailed assessment:

**Strengths**:
- Introduces a genuine mathematical concept (involution, function order) using only familiar proof techniques
- The comparison table (order 2 vs order 3) connects this level to the cyclic shift from earlier levels
- Previews group theory concepts without introducing group theory language
- The proof (`intro i; fin_cases i <;> rfl`) is appropriately simple -- the lesson is the concept, not the proof technique
- Strong `DisabledTactic` coverage (most restrictive in the world)
- Good transfer language in the conclusion

**Weaknesses**:
- Exploitable by `trivial` (same as all other levels)
- No hints for the `<;> rfl` optimization (minor: the step-by-step version `fin_cases i` then `rfl` three times is natural)
- The connection to L09 (bijectivity) could be made explicit: "You proved the swap is bijective in L09. Now we show it has an additional property: it is its own inverse." But L09 proves bijectivity for the cyclic shift, not the swap. L11 proves injectivity+surjectivity for the swap. So there is a slight narrative gap: L10 talks about the swap as involution, but the learner has not yet proved the swap is a bijection -- that comes in L11. This ordering is acceptable since L10's proof does not depend on bijectivity.

**Verdict**: Well-constructed level. Enriches the world without disrupting the level ladder.
