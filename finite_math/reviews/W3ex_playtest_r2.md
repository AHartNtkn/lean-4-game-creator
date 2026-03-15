# Playtest Audit R2: W3_ex (FinThreeExamples)

**Auditor**: playtest-auditor
**Date**: 2026-03-15
**Round**: 2 (re-audit after complete rewrite)
**World files**: `Game/Levels/FinThreeExamples/L01_Enumerate.lean` through `L10_Boss.lean`
**Build status**: Compiles (verified -- `lake build` succeeds, 8124 jobs)
**Predecessor worlds**: FinIntro (12 levels), FinCompute (11 levels)
**World role**: Example / case-study world for `Fin 3`

---

## 1. Overall Verdict

**CONDITIONAL PASS -- two P0 defects must be fixed, but the world is structurally sound.**

The rewrite is a dramatic improvement over round 1. The world now has 10 levels with genuine multi-step interactive proofs, a proper boss, inventory declarations for all new items, `DisabledTactic` on every level blocking `decide`/`native_decide`/`simp`/`aesop`/`simp_all`, layered hints, and strong transfer narrative. The round 1 defects (every level exploitable by `decide`, zero inventory, no boss, unconstrained L03) are all resolved.

Two P0 defects remain:

1. **L01 and L02 are exploitable by `omega`**: `omega` is not disabled and closes both statements in a single tactic with zero engagement. The learner can type `omega` and skip the intended `fin_cases` + disjunction navigation (L01) or `fin_cases` + `norm_num` (L02) patterns entirely.

2. **L04 intended proof is a compound one-liner after `fin_cases`**: The reference proof `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)` is an opaque compound tactic that the learner must type correctly in full before getting feedback on any individual case. The hints offer both a step-by-step and a one-liner path, which partially mitigates this, but the reference proof in the level file is the compound version. This is a P1 (not P0) because the hints DO describe the step-by-step approach -- see detailed analysis below.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | All new items (`Fintype.card`, `Function.Injective`, `Function.Surjective`, `Function.Bijective`) have `NewDefinition` + `DefinitionDoc`. New tactics (`left`, `right`, `obtain`) have `TacticDoc`. New theorems (`Fin.val_castSucc`, `Fintype.card_prod`, `Fintype.card_fin`) have `TheoremDoc` + `NewTheorem`. V2 (exhaustion) is genuinely retrieved. Deducted 1 point for `omega` exploit undermining L01/L02 coverage. |
| 2. Granularity fit | 4 | Each level isolates one dominant lesson. The 10-level arc from enumeration through injectivity/surjectivity/bijectivity to a boss is well-paced. No level is too broad or too fine. |
| 3. Proof-move teaching | 3 | Disjunction navigation (`left`/`right`), `fin_cases` retrieval, contradiction via `congr_arg Fin.val` + `norm_num`, `obtain` for existential destruction, `constructor` for conjunctions -- all explicitly taught. Deducted 1 for L01/L02 omega bypass. |
| 4. Inventory design | 3 | All new items documented. `TheoremTab "Fin"` and `TheoremTab "Fintype"` organize theorems. `NewHiddenTactic first exfalso` in L04 is appropriate. Deducted 1 because `left`/`right` docs are introduced in L01 but the tactics are NNG4-baseline and probably should not be gated behind this world. |
| 5. Hint design and recoverability | 3 | Hints are now layered: visible strategy hints describe what to do, hidden hints give full tactic syntax. Each case of `fin_cases` has its own hint. L06 and L07 have good multi-step hint chains. Deducted 1 because no `Branch` alternatives exist for learners who try non-canonical approaches (e.g., `cases` instead of `fin_cases`). |
| 6. Progression (worked example -> practice -> boss) | 4 | Clear arc: L01-L02 (warm-up/retrieval), L03 (new construction pattern), L04-L05 (paired inj/surj on same function), L06-L07 (counterexample pair), L08 (counting), L09 (integration of L04+L05), L10 (boss on a NEW function requiring all skills). Excellent fading of support. |
| 7. Mathematical authenticity | 4 | Rich concretization of abstract concepts. Injectivity and surjectivity are made tangible through complete case enumeration. The dual pair L06/L07 (surjectivity fails Fin3->Fin4, injectivity fails Fin4->Fin3) is pedagogically excellent. Transfer language in every conclusion. |
| 8. Paper-proof transfer | 4 | Every conclusion translates the Lean proof to plain English. The boss conclusion includes a comprehensive skills-learned table and plain-language summaries for all 10 levels. |
| 9. Technical fit and maintainability | 3 | Compiles cleanly. `DisabledTactic` present on all levels. Deducted 1 for the `omega` exploit gap. |

**Average**: 3.4
**Minimum**: 3 (multiple categories)

Verdict: Meets the minimum bar (average >= 3, no category below 2) **conditional on fixing the two P0 defects**.

---

## 3. Coverage Gaps

### 3a. R1 P0 resolutions

| R1 defect | Status | Evidence |
|-----------|--------|----------|
| Every level exploitable by `decide` | **FIXED** | `DisabledTactic decide native_decide simp aesop simp_all` on every level. `decide` cannot close any level. |
| Zero inventory declarations | **FIXED** | `NewTactic left right` (L01), `NewDefinition Fintype.card` + `DefinitionDoc` (L01), `NewDefinition Function.Injective` + `DefinitionDoc` (L04), `NewDefinition Function.Surjective` + `DefinitionDoc` (L05), `NewDefinition Function.Bijective` + `DefinitionDoc` (L09), `NewTactic obtain` + `TacticDoc` (L06), `NewTheorem Fin.val_castSucc Fintype.card_prod Fintype.card_fin` + `TheoremDoc` (L06, L08). |
| No boss | **FIXED** | L10 is a boss requiring `constructor` + injectivity proof + surjectivity proof on a different function (swap, not cyclic shift). |
| Unconstrained L03 return type | **FIXED** | Statement is `exists p : Fin 3 x Fin 3, p.1 != p.2`, which pins the inequality constraint and prevents `exact default`. |

### 3b. New coverage gaps

| Gap | Severity | Detail |
|-----|----------|--------|
| `omega` closes L01 and L02 | **P0** | `omega` is available (inherited from FinIntro L01) and is not in the `DisabledTactic` list for L01 or L02. Tested: `example : forall i : Fin 3, i = 0 or i = 1 or i = 2 := by omega` compiles. The learner can bypass `fin_cases` + disjunction navigation entirely. |
| No `Branch` for `cases` vs `fin_cases` | P2 | A novice might try `cases i` instead of `fin_cases i`. No Branch or rescue hint exists. `cases i` produces a goal with a generic `Fin.mk val isLt` structure that is harder to work with. A Branch or at least a hint saying "Try `fin_cases` instead of `cases`" would help. |
| `norm_num` availability inconsistency | P2 | L05, L08, L09 disable `norm_num`; L01-L04, L06, L07, L10 do not. In L04, L07, and L10, `norm_num` is part of the intended proof (used inside `congr_arg Fin.val h; norm_num at this`). But in L05, `norm_num` is disabled, and `rfl` is used to close the witness goals. This is consistent with the different proof patterns, but a learner might be confused about when `norm_num` is available. |

### 3c. Coverage closure assessment

| Item | Axis | Coverage states achieved |
|------|------|-------------------------|
| `Fin 3` concretization | EXAMPLE | I (L01), S (L02-L09), G (L10) -- strong |
| `fin_cases` retrieval | MOVE/LEAN | R (L01-L07), G (L09-L10) -- strong |
| Disjunction navigation (`left`/`right`) | MOVE/LEAN | I (L01) -- only appears in L01, not retrieved later. Weak closure but acceptable for an example world. |
| `congr_arg Fin.val h` contradiction pattern | MOVE | I (L03), S (L04), R (L07), G (L10) -- strong |
| `Function.Injective` | MATH | I (L04), R (L09), G (L10) -- adequate |
| `Function.Surjective` | MATH | I (L05), counterexample (L06), R (L09), G (L10) -- strong |
| `Function.Bijective` | MATH | I (L09), G (L10) -- adequate |
| `obtain` for existential destruction | LEAN | I (L06) -- introduced but not retrieved in this world. Will be retrieved in later worlds. |
| `Fintype.card_prod`, `Fintype.card_fin` | MATH/LEAN | I (L08) -- preview for later counting worlds. |
| Pigeonhole preview | TRANSFER | Present in L06 (surj fails) and L07 (inj fails) conclusions. Not a formal proof but good narrative setup. |

---

## 4. Granularity Defects

### 4a. Level-by-level granularity

| Level | Dominant lesson | One-sentence test | Verdict |
|-------|----------------|-------------------|---------|
| L01 | Exhaustive enumeration of `Fin 3` with disjunction | "Prove all elements of `Fin 3` are 0, 1, or 2 via `fin_cases` + `left`/`right`" | Pass (if omega is blocked) |
| L02 | Function evaluation by cases | "Check a property case-by-case using `fin_cases` + `norm_num`" | Pass (if omega is blocked) |
| L03 | Existential witness with constrained property | "Construct a specific pair and prove an inequality via contradiction" | Pass |
| L04 | Injectivity proof by double exhaustion | "Prove injectivity by checking all 9 input pairs" | Pass |
| L05 | Surjectivity proof by finding preimages | "Prove surjectivity by exhibiting a preimage for each output" | Pass |
| L06 | Surjectivity disproof | "Disprove surjectivity by extracting and refuting a preimage" | Pass |
| L07 | Injectivity disproof | "Disprove injectivity by finding a collision and deriving contradiction" | Pass |
| L08 | Cardinality of product types | "Count elements via `card_prod` and `card_fin` rewrites" | Pass |
| L09 | Bijectivity = injectivity + surjectivity | "Combine L04 and L05 patterns via `constructor`" | Pass |
| L10 | Boss: integration on a new function | "Prove inj+surj for a different permutation using all prior patterns" | Pass |

### 4b. World coherence

The world has a coherent center of gravity: **concrete reasoning about functions on `Fin 3`** via exhaustive case analysis. The level ladder progresses logically:
- L01-L02: warm-up (retrieving `fin_cases` on concrete tasks)
- L03: construction (existential witness)
- L04-L05: positive properties (injectivity, surjectivity)
- L06-L07: negative properties (disproving inj/surj) -- counterexample thinking
- L08: counting
- L09: integration (bijectivity = inj + surj)
- L10: boss (same skills, different function)

No splitting needed. The world covers one coherent theme with steady escalation.

### 4c. Novelty budget check

| Level | New math | New proof move | New Lean move | New notation | Budget ok? |
|-------|----------|---------------|---------------|-------------|-----------|
| L01 | None | Disjunction navigation | `left`, `right` | None | Yes (1 new Lean move) |
| L02 | None | None (retrieval) | None | None | Yes |
| L03 | Product type pairs | Inequality via `congr_arg` | `refine <..., ?_>` | Angle brackets | Borderline: 2 new things (pair construction + inequality pattern). But the inequality pattern was previewed in FinIntro L12 (`congr_arg`). |
| L04 | `Function.Injective` | Double `fin_cases` + contradiction closer | `NewHiddenTactic exfalso first` | None | Borderline: new math (Injective) + new proof move (double fin_cases). But the math is explained in the intro and the proof move reuses `fin_cases` from prior world. |
| L05 | `Function.Surjective` | Preimage finding | None | None | Yes |
| L06 | None | Surjectivity disproof | `obtain` | None | Borderline: new tactic + new proof pattern. `obtain` is close to `rcases` which is baseline. |
| L07 | None | Injectivity disproof via collision | None | None | Yes |
| L08 | `Fintype.card_prod`, `card_fin` | Rewriting with card lemmas | None | None | Yes |
| L09 | `Function.Bijective` | Integration (constructor + inj + surj) | None | None | Yes (integration, not new novelty) |
| L10 | None | None (boss) | None | None | Yes (boss integrates) |

L03, L04, and L06 are at the edge of the novelty budget. L04 is the most concerning: it introduces `Function.Injective` (new definition), double `fin_cases` (new proof shape), and the `exfalso; congr_arg; norm_num` contradiction closer (new pattern). However, each component is individually familiar (`fin_cases` from FinCompute, `congr_arg` from FinIntro L12, `norm_num` from FinCompute L05), and the level intro explains the assembly clearly. The hints provide both step-by-step and compound approaches. **Acceptable but tight.**

---

## 5. Statement Exploitability

### Level-by-level analysis

| Level | Statement | Exploitable? | Detail |
|-------|-----------|-------------|--------|
| L01 | `forall i : Fin 3, i = 0 or i = 1 or i = 2` | **YES -- P0** | `omega` closes it in one tactic. `omega` is not disabled. |
| L02 | `forall i : Fin 3, (2 * i.val + 1) % 2 = 1` | **YES -- P0** | `omega` closes it in one tactic. `omega` is not disabled. |
| L03 | `exists p : Fin 3 x Fin 3, p.1 != p.2` | No | `decide` disabled. `omega` does not close it (tested). `exact default` does not work because `Fin 3 x Fin 3` has no `Inhabited`-to-proof path for the existential. The learner must provide a witness AND prove the inequality. |
| L04 | `Function.Injective (fun i : Fin 3 => match ...)` | No | `decide`/`simp` disabled. `omega` does not close it after `fin_cases` (tested). Requires the intended double-`fin_cases` + contradiction pattern. |
| L05 | `Function.Surjective (fun i : Fin 3 => match ...)` | No | `decide`/`simp`/`norm_num` all disabled. Must provide explicit witnesses via `exact <witness, rfl>`. |
| L06 | `not Function.Surjective (Fin.castSucc : Fin 3 -> Fin 4)` | No | `decide`/`simp` disabled. Requires `intro h; obtain; fin_cases a` pattern. `omega` cannot close the subgoals after `fin_cases` (tested). |
| L07 | `not Function.Injective (fun i : Fin 4 => match ...)` | No | `decide`/`simp` disabled. Requires finding the collision and deriving contradiction. `omega` cannot close the whole thing. |
| L08 | `Fintype.card (Fin 3 x Fin 3) = 9` | No | `decide`/`simp`/`norm_num` all disabled. Must use the `rw` steps. (After `rw [Fintype.card_prod, Fintype.card_fin]`, `3 * 3 = 9` reduces by `rfl`, which is fine.) |
| L09 | `Function.Bijective (fun i : Fin 3 => match ...)` | No | `decide`/`simp`/`norm_num` all disabled. Must use `constructor` + injectivity + surjectivity patterns. |
| L10 | `Function.Injective ... and Function.Surjective ...` | No | `decide`/`simp` disabled. Same as L09 pattern on a different function. `omega` does not close subgoals (tested). |

**Summary**: 2 of 10 levels are exploitable (L01, L02), down from 5 of 6 in R1. The fix is straightforward: add `omega` to the `DisabledTactic` list for L01 and L02.

---

## 6. Interactive Proof Quality

| Level | Intended steps | Interactive? | Notes |
|-------|---------------|-------------|-------|
| L01 | `intro i` -> `fin_cases i` -> 3x (`left`/`right` + `rfl`) | Yes | Each step produces visible goal changes. The disjunction navigation is genuinely interactive. |
| L02 | `intro i` -> `fin_cases i` -> 3x `norm_num` | Yes | Clear step-by-step structure. Each case shows a concrete numeric goal. |
| L03 | `refine <(0,1), ?_>` -> `intro h` -> `have hv := congr_arg Fin.val h` -> `norm_num at hv` | Yes | Four distinct steps with visible state changes. Good. |
| L04 | `intro a b h` -> `fin_cases a <;> fin_cases b` -> 9 subgoals | **Mixed** | The reference proof uses `<;> first | rfl | (exfalso; ...)` as a compound closer. But hints describe the step-by-step alternative. A learner CAN do it step by step (3 case blocks, each with 3 subcases). The compound version is an optimization, not a requirement. **P2**: The reference proof should be the step-by-step version, with the compound version in a hidden hint. |
| L05 | `intro b` -> `fin_cases b` -> 3x `exact <witness, rfl>` | Yes | Clean interactive structure. |
| L06 | `intro h` -> `obtain <a, ha> := h <3, by omega>` -> `fin_cases a <;> norm_num [...]  at ha` | **Mixed** | The `obtain` step is one moderately complex expression. After that, the compound `<;>` closer handles all 3 cases. Acceptable because the `obtain` pattern is clearly taught in the hint chain. The compound closer is fine here (3 identical subgoals). |
| L07 | `intro h` -> `have h03 := h rfl` -> `have := congr_arg Fin.val h03` -> `norm_num at this` | Yes | Four clear steps. The learner builds the collision, extracts the value-level equation, and derives contradiction. Excellent interactive flow. |
| L08 | `rw [Fintype.card_prod]` -> `rw [Fintype.card_fin]` | Yes | Two clean rewrites. After the second, the goal `3 * 3 = 9` closes automatically (definitional equality). Simple but effective. |
| L09 | `constructor` -> (injectivity block) -> (surjectivity block) | Yes | Integration level. The learner types `constructor`, then applies the L04 and L05 patterns. Good structure. |
| L10 | `constructor` -> (injectivity block) -> (surjectivity block) | Yes | Boss. Same structure as L09 but on a different function (swap, not cyclic shift), so preimages differ. The learner must think about which element maps where. |

**Red flags**:
- L04's reference proof compound closer: P2 (medium). The hints rescue this by describing step-by-step, but the reference proof in the file should be the interactive version.
- L06's `obtain <a, ha> := h <3, by omega>` expression: borderline. It requires typing a moderately complex expression before getting feedback. But the hint gives the exact syntax, and this is the first `obtain` introduction, so explicitness is appropriate.

---

## 7. Learner Simulation

### Attentive novice

**First likely stuck point**: L03 (Pair construction). The goal `exists p : Fin 3 x Fin 3, p.1 != p.2` requires the learner to:
1. Choose a witness pair
2. Use `refine` with angle brackets
3. Prove the inequality via the `congr_arg` + `norm_num` pattern

The `refine <(0, 1), ?_>` syntax with nested angle brackets is new. The hint gives it explicitly, which is appropriate for a first encounter. But if the learner tries `use (0, 1)` (which should work as an alternative), no hint covers that path.

**Rescue path**: The hint chain is complete for the canonical path. Missing: `use` as an alternative to `refine` for existential witnesses.

**Most likely wrong move**:
- L01: Typing `omega` (which works -- P0 exploit).
- L04: Typing `intro a b h; cases a` instead of `fin_cases a`. `cases` produces a harder goal structure. No rescue hint.
- L06: Trying `omega` or `contradiction` after `intro h` instead of `obtain`.

**Lesson legibility**: Each level's intro clearly states what the learner should learn. The conclusions reinforce the lesson with a summary and plain-language translation. This is a strength of the world.

### Experienced Lean user

**Avoidable friction**: L01 and L02 are trivial for an experienced user even with `omega` disabled (just `fin_cases` + closer). The experienced user will find these easy but not annoying -- they are warm-up levels.

**Alias gaps**:
- L03: `use` works instead of `refine`, but no alias support.
- L04: `simp` would close contradictory cases but is disabled. This is intentional (forcing the manual pattern). `omega` does not work for the Fin-level contradictions. Good.
- L07: `have h03 := h rfl` -- an experienced user might try `exact absurd (h rfl) (by omega)` or `apply absurd (h rfl)` + closer. These work but are not hinted.

**Inventory clutter**: Manageable. The world adds `left`, `right`, `obtain` (tactics), `Fintype.card`, `Function.Injective`, `Function.Surjective`, `Function.Bijective` (definitions), `Fin.val_castSucc`, `Fintype.card_prod`, `Fintype.card_fin` (theorems), and `first`, `exfalso` (hidden). This is a lot for one world but each item is well-documented and used in context.

**Needless forced verbosity**: L04's intended proof requires typing `exfalso; have := congr_arg Fin.val h; norm_num at this` for each contradictory case (6 times). The `<;>` combinator handles this, but it is still verbose. This is inherent to exhaustive proofs and acceptable.

---

## 8. Boss Integrity (L10)

### Seeded subskills check

| Subskill | Where seeded | Boss usage |
|----------|-------------|------------|
| `constructor` to split conjunction | L09 (and FinCompute boss) | Required as first step |
| `intro a b h; fin_cases a <;> fin_cases b` (double exhaustion) | L04 (first contact), L09 (retrieval) | Required for injectivity |
| `exfalso; congr_arg Fin.val h; norm_num at this` (contradiction closer) | L03 (intro), L04 (supported), L07 (retrieval) | Required for off-diagonal cases |
| `rfl` for diagonal cases | L04, L09 | Required for diagonal cases |
| `intro b; fin_cases b; exact <_, rfl>` (preimage finding) | L05 (first contact), L09 (retrieval) | Required for surjectivity |

**All subskills are seeded and practiced before the boss.** No lottery moves.

### Integration quality

The boss uses a **different function** (swap: `0->0, 1->2, 2->1`) than the training levels (cyclic shift: `0->1, 1->2, 2->0`). This forces the learner to:
- Determine which pairs give contradictions vs trivial equalities (different from the cyclic shift)
- Find different preimages (`1 = f 2`, `2 = f 1`, not `1 = f 0`, etc.)

This is genuine integration, not just replay. The function is different enough that the learner must think about the specific values, not just replay the pattern mechanically.

### Gauntlet check

Is this a gauntlet boss (just concatenating L04 + L05 without new integration demand)? Partially yes: the boss IS structurally identical to L09 (bijectivity) but on a new function. L09 uses the same cyclic shift as L04/L05, so it IS a gauntlet. But L10 uses a DIFFERENT function, which adds planning challenge (different preimage assignments, different collision structure).

**Verdict**: Borderline acceptable. The boss does require the learner to re-derive preimage mappings for a new function, which is a genuine (if modest) planning challenge. A stronger boss might require an additional integrating element (e.g., also proving a counting fact or combining injectivity with a cardinality argument). But for an example world with no plan-specified boss, this is adequate.

### Boss surprise burden

None. Every tactic and proof pattern in the boss was used in L04-L09. The proof is 5 distinct steps (constructor, injectivity block, surjectivity block), all of which are practiced. The boss is slightly shorter than L09 (same structure but the swap function has simpler cases). No surprise.

### Can the learner explain why?

Yes. "The swap function sends 0 to 0, 1 to 2, and 2 to 1. It is injective because the three outputs 0, 2, 1 are all distinct. It is surjective because every element has a preimage: 0 = f(0), 1 = f(2), 2 = f(1)." This is exactly what the conclusion says.

---

## 9. Course-Role Sanity

**Intended role**: Example / case-study world.

**Actual role**: Example / case-study world. **Correctly cast.**

The world:
- Grounds abstract theory (`Fin n`, injectivity, surjectivity) in concrete computation on `Fin 3` -- YES
- Requires the learner to DO the concrete computation (not delegate to automation) -- YES (with the omega caveat on L01/L02)
- Builds intuition through hands-on case-by-case engagement -- YES
- Retrieves `fin_cases` from prior world on new ground -- YES
- Introduces "the same object through a different theoretical lens" (injectivity, surjectivity, counting, bijectivity) -- YES
- Includes counterexample thinking (L06, L07) -- YES
- Has strong transfer language throughout -- YES

The dual pair L06/L07 is especially well-cast: it previews the pigeonhole principle by showing that maps between differently-sized finite types cannot be surjective/injective. This is excellent foreshadowing for the later counting world (W12).

---

## 10. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| `omega` exploits L01 and L02 | **P0** | `omega` closes both statements in one tactic. Add `omega` to `DisabledTactic` for L01, L02. Consider adding it to all levels for consistency (it is not needed in any intended proof in this world). |
| L08 `rw [Fintype.card_fin]` closes the entire goal | P3 (cosmetic) | After `rw [Fintype.card_prod]; rw [Fintype.card_fin]`, the goal `3 * 3 = 9` closes by definitional reduction. This is actually fine -- the lesson is the two rewrites, not the arithmetic. |
| L04/L09/L10 reference proofs use compound `<;>` closers | P2 | The reference proof `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)` is correct but hostile to step-by-step exploration. The hints describe both approaches. The step-by-step version should be the reference proof in the file. |
| No `Branch` for `use` vs `refine` in L03 | P2 | `use (0, 1)` is a valid alternative to `refine <(0, 1), ?_>`. No Branch or hint covers this. |
| No rescue hint for `cases` vs `fin_cases` | P2 | Novice may try `cases i` which produces harder goals. No rescue hint. |
| `left`/`right` introduced as `NewTactic` | P3 | These are arguably NNG4-baseline tactics. Introducing them here is conservative but not wrong. |
| `norm_num` disabled in L05 but available in L04 | P3 | Consistency nit. L05 disables `norm_num` (forcing `rfl` for the preimage proofs), while L04 uses `norm_num` in the contradiction closer. Both choices are defensible in context. |

---

## 11. Ranked Patch List

### P0 (blocking -- must fix)

1. **Add `omega` to `DisabledTactic` in L01 and L02.** Change:
   - L01: `DisabledTactic decide native_decide simp aesop simp_all` -> `DisabledTactic decide native_decide simp aesop simp_all omega`
   - L02: `DisabledTactic decide native_decide simp aesop simp_all` -> `DisabledTactic decide native_decide simp aesop simp_all omega`

   Also consider adding `omega` to ALL levels in this world for consistency, since no intended proof uses `omega` as a top-level closer (only `by omega` inside `obtain` in L06, which is a subproof context and should still work even if `omega` is globally disabled at the tactic level -- needs testing).

   **IMPORTANT**: Verify that `by omega` inside `obtain <a, ha> := h <3, by omega>` in L06 still works when `omega` is in `DisabledTactic`. If `DisabledTactic` blocks `omega` even in `by` subproofs, L06 will break. In that case, L06 needs its `DisabledTactic` to omit `omega`, or the `<3, by omega>` needs to be replaced with `(⟨3, by omega⟩ : Fin 4)` using a term-mode proof that does not invoke the tactic.

### P1 (high -- should fix)

2. **Make L04's reference proof step-by-step.** Replace the compound `fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; ...)` with the step-by-step version (3 top-level case blocks, each with 3 subcases). Move the compound version to a hidden hint. This makes the reference proof match the interactive experience better.

### P2 (medium -- nice to fix)

3. **Add a `Branch` in L03 for `use (0, 1)` as an alternative to `refine <(0, 1), ?_>`.** The branch should include its own hints for the inequality proof.

4. **Add a rescue hint in L01 for learners who try `cases i`.** After the `intro i` hint, add: `Hint (hidden := true) "If you tried \`cases i\`, the goal structure is harder to work with. Try \`fin_cases i\` instead --- it produces one goal per element of the finite type."`

5. **Add `omega` to `DisabledTactic` in L03--L10 for consistency** (if verified not to break L06's `by omega` subproof).

### P3 (low -- optional)

6. **Consider whether `left`/`right` should be `NewTactic` here.** If they are already unlocked from NNG4 or another source, remove `NewTactic left right` to avoid suggesting they are new. If they are genuinely first-contact, keep them.

7. **Add a `Branch` in L04 for the step-by-step proof path.** The compound `<;>` closer and the step-by-step case-by-case closer should both be supported with hints.

---

## 12. What to Playtest Again After Patching

After implementing patches 1-2:

1. **Verify `omega` is blocked in L01 and L02.** Test that `omega` alone fails on both statements when `DisabledTactic` includes `omega`.
2. **Verify L06 `by omega` subproof still works.** If `DisabledTactic omega` blocks `by omega` inside `obtain`, the patch needs adjustment.
3. **Verify L04's step-by-step reference proof compiles.** After splitting the compound closer into explicit case blocks.
4. **Re-run the full build.** Confirm all 10 levels compile after changes.
5. **Quick exploitability re-scan.** After `omega` is blocked, confirm no other single-tactic exploit remains (e.g., `tauto`, `trivial`, `ring`).

---

## 13. Summary of Defect Counts

| Severity | Count | R1 comparison |
|----------|-------|---------------|
| P0 (blocking) | 1 (omega exploit on L01/L02) | Down from 4 |
| P1 (high) | 1 (L04 compound reference proof) | Down from 3 |
| P2 (medium) | 3 (Branch for `use`, rescue for `cases`, consistency of omega disabling) | Down from 3 |
| P3 (low) | 3 (left/right NewTactic, norm_num consistency, L08 cosmetic) | New category |
| **Total** | **8** | **Down from 10** |

## 14. Comparison with Round 1

The world has been transformed. Here is the delta:

| Dimension | R1 | R2 |
|-----------|----|----|
| Levels | 6 | 10 |
| Boss | None | L10 (swap permutation, requires inj + surj integration) |
| DisabledTactic coverage | 0/6 levels | 10/10 levels |
| Inventory declarations | 0 | 7 definitions + 3 theorems + 3 tactics + 2 hidden tactics |
| Exploitable levels | 5/6 | 2/10 (omega only) |
| Multi-step proofs | 0/6 | 10/10 |
| Layered hints | 0/6 | 8/10 |
| Transfer language | Good (in text) | Good (in text AND in proof experience) |
| Rubric average | 1.3 | 3.4 |
| Rubric minimum | 0 | 3 |

The R1 verdict was "FAIL -- requires significant rework." The R2 verdict is "CONDITIONAL PASS." The remaining P0 (omega exploit) is a surgical fix (add one word to two `DisabledTactic` lines). After that fix, this world is ready for integration.
