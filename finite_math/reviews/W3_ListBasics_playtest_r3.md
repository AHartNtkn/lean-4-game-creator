# Playtest Audit (Round 3): W3 ListBasics

**Auditor**: playtest-auditor (adversarial)
**World**: W3 -- Lists: construction and operations
**World type**: Lecture
**Levels audited**: L01 through L11 (11 levels)
**Build status**: Compiles (verified -- `lake build` succeeds, 8120 jobs, 0 errors)
**Prior audits**: `W3_ListBasics_playtest.md` (R1 -- FAILING), `W3_ListBasics_playtest_r2.md` (R2 -- CONDITIONAL PASS)

---

## 0. Prior Issue Resolution Check

### R2 P0 Issues

| R2 # | R2 P0 Issue | Status in R3 | Detail |
|-------|------------|--------------|--------|
| 1 | `aesop` not disabled anywhere -- closes L03-L11 in one step | **FIXED** | `aesop` now appears in `DisabledTactic` on ALL 11 levels. Confirmed via grep: every level file has `aesop` in its `DisabledTactic` line. |

### R2 P1 Issues

| R2 # | R2 P1 Issue | Status in R3 | Detail |
|-------|------------|--------------|--------|
| 2 | `simp` not disabled on L02 -- bypasses `rw [List.length_cons]` | **FIXED** | L02 now has `DisabledTactic decide native_decide simp aesop`. |
| 3 | `simp` not disabled on L07 -- bypasses `rw [List.length_append]` | **FIXED** | L07 now has `DisabledTactic decide native_decide simp aesop`. |
| 4 | `simp` closes L09 (Nodup level) in one step | **NOT FIXED** | L09 still has `DisabledTactic decide native_decide aesop` -- no `simp`. Bare `simp` at the top level should still close the entire 8-step proof. R2 recommended option (a) as acceptable: `simp` is part of the intended proof for non-membership subgoals, and `simp` is being taught in this level (`NewTactic simp`). See detailed analysis below. |

### R1 P0 Issues (sanity re-check)

| R1 # | R1 P0 Issue | R2 Status | R3 Status |
|-------|------------|-----------|-----------|
| 1 | All statements concrete/decidable | Fixed in R2 | Still fixed. 9/11 levels use symbolic/universally-quantified statements. |
| 2 | `decide`/`simp` not gated | Fixed in R2 | Still fixed. `decide` and `native_decide` disabled everywhere. `simp` disabled on 9/11 levels (all except L01, L08, L09). |
| 3 | `List.Nodup` (M17) missing | Fixed in R2 | Still fixed. L09 is dedicated Nodup level. |
| 4 | Fake boss | Fixed in R2 | Still fixed. L11 requires 7-step integration proof. |

**All R2 P0 issues are resolved. Two of three R2 P1 issues are resolved. One R2 P1 issue (L09 `simp` exploit) remains by design choice.**

---

## 1. Overall Verdict

**PASS.** The world is a solid teaching instrument. All prior P0 defects are resolved. The `aesop` gate is now in place on every level. The `simp` gate has been added to L02 and L07 as recommended. The remaining `simp` availability on L09 is a deliberate pedagogical choice (L09 is where `simp` is first taught via `NewTactic simp`), and while it allows a one-shot bypass, this is acceptable because: (a) the learner is being taught `simp` in that level, (b) the introduction explicitly explains the step-by-step approach, and (c) a learner who types bare `simp` at the top has at least used the tactic the level is partly about -- even if they missed the `nodup_cons` unfolding pattern.

There are residual P2 issues (library one-liner bypasses, no `DisabledTheorem`, no `Branch` for alternative paths), but none are blocking. The world is shippable.

---

## 2. Rubric Scores

| Category | R1 | R2 | R3 | Notes |
|----------|----|----|-----|-------|
| 1. Coverage closure | 1 | 3 | 3 | No change from R2. Coverage map: M16 (I, S, G), M17 (I), N11 (I, S), N12 (I, S). |
| 2. Granularity fit | 1 | 3 | 3 | No change from R2. Each level isolates one dominant lesson. L07/L08 remain thin but justified. |
| 3. Proof-move teaching | 0 | 4 | 4 | No change. `rw`, `left`/`right`, `constructor`, `refine`, `exact` all taught and practiced. |
| 4. Inventory design | 2 | 3 | 3+ | Improved by `aesop`/`simp` gating. Inventory is now properly controlled: the learner cannot bypass lessons via ungated automation. `simp` availability on L09 is deliberate (it is being taught there). |
| 5. Hint design and recoverability | 1 | 3 | 3 | No change. Hints guide step-by-step. No `Branch` for common wrong paths (still P2). |
| 6. Worked example -> practice -> transfer -> boss | 0 | 3 | 3 | No change. Clear L01 warmup -> L02-L06 first-contact -> L07-L08 retrieval -> L09 new concept -> L10 combination -> L11 boss. |
| 7. Mathematical authenticity | 2 | 4 | 4 | No change. |
| 8. Paper-proof transfer | 2 | 3 | 3 | No change. |
| 9. Technical fit and maintainability | 2 | 3 | 3+ | Improved: tactic gating is now comprehensive and deliberate. |

**Average: 3.3.** All categories >= 3. No automatic red flags triggered.

---

## 3. Tactic Gating Verification (Primary Focus of R3)

This is the central question for R3: is the `aesop` gate properly applied, and are `simp` gates correct?

### 3a. Level-by-level DisabledTactic inventory

| Level | `decide` | `native_decide` | `simp` | `aesop` | Correct? |
|-------|----------|-----------------|--------|---------|----------|
| L01 | YES | YES | no | YES | CORRECT. L01 is `rfl`; `simp` does not add bypass risk. |
| L02 | YES | YES | YES | YES | CORRECT. L02 teaches `rw [List.length_cons]`; `simp` was the bypass. Now blocked. |
| L03 | YES | YES | YES | YES | CORRECT. |
| L04 | YES | YES | YES | YES | CORRECT. |
| L05 | YES | YES | YES | YES | CORRECT. |
| L06 | YES | YES | YES | YES | CORRECT. |
| L07 | YES | YES | YES | YES | CORRECT. L07 teaches `rw [List.length_append]`; `simp` was the bypass. Now blocked. |
| L08 | YES | YES | no | YES | CORRECT. L08 is `rfl`; `simp` does not add bypass risk. |
| L09 | YES | YES | **no** | YES | ACCEPTABLE. L09 is the `NewTactic simp` level. `simp` is part of the intended proof. See section 3b. |
| L10 | YES | YES | YES | YES | CORRECT. |
| L11 | YES | YES | YES | YES | CORRECT. Boss cannot be bypassed by any gated tactic. |

### 3b. L09 `simp` analysis (the one remaining question)

**Intended proof for L09** (`[1, 2, 3].Nodup`):
```
rw [List.nodup_cons]       -- split into 1 ∉ [2,3] ∧ [2,3].Nodup
constructor                -- handle conjunction
· simp                     -- evaluate 1 ∉ [2,3] concretely
· rw [List.nodup_cons]     -- split [2,3].Nodup
  constructor
  · simp                   -- evaluate 2 ∉ [3]
  · rw [List.nodup_cons]
    constructor
    · simp                 -- evaluate 3 ∉ []
    · exact List.nodup_nil -- base case
```

**Exploit**: bare `simp` at the top level closes the entire goal in one step. The learner skips the entire `nodup_cons` unfolding pattern.

**Assessment**: This is a tension between two legitimate pedagogical goals:
1. Teaching `simp` as a tool (hence `NewTactic simp` in this level)
2. Teaching the `nodup_cons` recursive unfolding pattern

The level tries to do both. The introduction explicitly says "use `simp` for the concrete non-membership checks" and walks through the step-by-step approach. A learner who reads the introduction and follows the guided path will learn the pattern. A learner who types bare `simp` immediately has at minimum used the tactic being taught, even if they missed the structural lesson.

**Severity**: P2. This is an imperfect trade-off but acceptable for a lecture world. The `nodup_cons` pattern is reinforced conceptually in the conclusion (which explains the recursive structure), and the real test of `Nodup` understanding will come in later worlds (W4 Multisets, where `Nodup` is used structurally).

**Would disabling `simp` here work?** Not straightforwardly. The intended proof uses `simp` for the non-membership subgoals (`1 ∉ [2, 3]`, etc.). If `simp` were disabled, the learner would need another way to evaluate these concrete membership propositions. `decide` is already disabled. `norm_num` does not handle list membership. The alternatives would be:
- Manual proof: `intro h; rw [List.mem_cons] at h; cases h with ...` -- far too complex for L09's scope
- Adding `norm_num` extensions for list membership -- fragile
- Restructuring with symbolic lists and hypotheses -- changes the level entirely

The current design is the pragmatic choice. Mark as accepted.

### 3c. Residual automation paths (non-gated)

After gating `decide`, `native_decide`, `simp`, and `aesop`, what automation paths remain?

| Tactic | Available? | Can it close any level? | Risk |
|--------|-----------|------------------------|------|
| `omega` | Yes | No level has a pure arithmetic goal | None |
| `norm_num` | Yes | L01 (but `rfl` already works); L08 (but `rfl` already works) | None |
| `ring` | Yes | No level has a ring-algebra goal | None |
| `tauto` | Yes (if from Mathlib) | L03: `5 ∈ 5 :: l` -- unclear if `tauto` can handle list membership. Unlikely. | Very low |
| `trivial` | Yes | Unlikely to close any level | Very low |
| `exact?` / `apply?` | Yes (search tactics) | Would find library one-liners. See section 5. | P2 (search tactics are learning tools, not bypasses) |

**Verdict**: No ungated automation tactic poses a P0 or P1 risk. The tactic gating is comprehensive.

---

## 4. Statement Exploitability (Section 1b)

### 4a. Automation exploits (post-gating)

| Level | `decide` | `simp` | `aesop` | Remaining exploit? |
|-------|----------|--------|---------|-------------------|
| L01 | Disabled | Available (but `rfl` is fine) | Disabled | None. `rfl` is appropriate. |
| L02 | Disabled | **Disabled** | Disabled | None. Only `rw [List.length_cons]` works. |
| L03 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |
| L04 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |
| L05 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |
| L06 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |
| L07 | Disabled | **Disabled** | Disabled | None. Only `rw [List.length_append]` works. |
| L08 | Disabled | Available (but `rfl` is fine) | Disabled | None. |
| L09 | Disabled | **Available -- closes in 1 step** | Disabled | P2 (deliberate; see 3b). |
| L10 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |
| L11 | Disabled | Disabled | **Disabled** | Library one-liner (see 4b). |

### 4b. Library-lemma one-liner exploits (unchanged from R2)

| Level | One-liner | Bypasses lesson? | Severity |
|-------|-----------|-----------------|----------|
| L03 | `exact List.mem_cons_self 5 l` | Yes -- skips `rw [List.mem_cons]` + `left` + `rfl` | P2 |
| L04 | `exact List.mem_append_left _ h` | Yes -- skips `rw [List.mem_append]` + `left` + `exact` | P2 |
| L05 | `exact List.mem_map_of_mem f h` | Yes -- skips `rw [List.mem_map]` + `refine` + `rfl` | P2 |
| L06 | `exact List.mem_filter.mpr ⟨hmem, hpred⟩` | Yes -- skips `rw [List.mem_filter]` + `constructor` + `exact` | P2 |
| L10 | `exact List.mem_cons_of_mem _ (List.mem_append_right _ h)` | Yes -- skips all 5 steps | P2 |
| L11 | `exact List.mem_filter.mpr ⟨List.mem_map_of_mem f h, hp⟩` | Yes -- boss one-liner | P2 |

**Why P2 and not P1**: These library lemmas are the "compiled" versions of exactly the proof patterns the levels teach. A post-NNG4 learner is unlikely to know `List.mem_cons_self`, `List.mem_append_left`, or `List.mem_map_of_mem`. These are Mathlib API lemmas that require knowing the exact name. A learner who discovers them via `exact?` has at least engaged with a search process. The pedagogical risk is real but low-probability.

**Recommendation** (unchanged from R2): Add `DisabledTheorem` for these shortcut lemmas on the relevant levels. This is a polish item, not a blocker.

---

## 5. Interactive Proof Quality (Section 1c)

No change from R2. Every multi-step level provides visible goal-state changes after each tactic step. The learner can explore incrementally.

### 5a. Re-check for elaborate one-liners

| Level | Longest single tactic | Elaborateness | Verdict |
|-------|----------------------|---------------|---------|
| L05 | `refine ⟨a, h, ?_⟩` | Medium -- 3 components in angle brackets | Acceptable. Taught in this level with hints. Alternative `exact ⟨a, h, rfl⟩` is mentioned but not the guided path. |
| L09 | `exact List.nodup_nil` | Low | Fine. |
| L11 | `refine ⟨a, h, ?_⟩` | Medium | Retrieval from L05. |

No red flags. All proof steps are short and produce visible feedback.

### 5b. Opaque goals check

After `rw [List.mem_cons]` in L03, the goal displays `5 = 5 ∨ 5 ∈ l` -- clear and concrete. After `rw [List.mem_filter]` in L06, the goal displays `a ∈ l ∧ p a = true` -- clear. After `rw [List.mem_map]` in L05, the goal displays `∃ a_1 ∈ l, f a_1 = f a` -- clear but uses auto-generated name `a_1`. This is a minor display issue but not confusing because the hint explains what the goal means.

No opaque goals detected.

---

## 6. Coverage Analysis

### 6a. Coverage item status (unchanged from R2)

| Item | Axis | Status | Coverage States Achieved |
|------|------|--------|-------------------------|
| M16 (List basic API) | MATH | Complete | I (L01), S (L02-L07), G (L11) |
| M17 (List.Nodup) | MATH | Introduced | I (L09) |
| N11 (`::` notation) | NOTATION | Introduced + practiced | I (L01), S (L02, L03) |
| N12 (`++` notation) | NOTATION | Introduced + practiced | I (L04), S (L07, L10) |
| V1 (unfolding definitions via `rw`) | MOVE | Core pattern | Practiced in L02-L07, L09-L11 |
| V-left/right (disjunction navigation) | MOVE | Introduced + practiced | I (L03), S (L04, L10) |
| V-constructor (conjunction splitting) | MOVE | Introduced + practiced | I (L06), S (L09, L11) |
| V-refine (partial witness) | MOVE | Introduced + practiced | I (L05), S (L11) |
| `simp` (automation tactic) | LEAN | Introduced | I (L09) |

### 6b. Coverage gaps (minor, unchanged from R2)

| Gap | Severity | Detail |
|-----|----------|--------|
| No counterexample for `Nodup` failure | P2 | L09 conclusion discusses `[1,2,1]` failing `Nodup` verbally but doesn't prove it. A level proving `¬ [1,2,1].Nodup` would concretize the concept. |
| `have` tactic not exercised | P2 | Not required in any level. Acceptable since `constructor` serves a similar structural role. |
| No `Branch` for alternative proof paths | P2 | Learners who try `use` instead of `refine` in L05, or `Or.inl` instead of `left` in L03, get no guidance. |
| Focused subgoal syntax (`·`) not documented | P2 | Used in L06, L09, L11 guided proofs but no `TacticDoc`. |

---

## 7. Granularity Analysis

### 7a. Level-by-level review (unchanged from R2)

| Level | Dominant Lesson | Steps | Verdict |
|-------|----------------|-------|---------|
| L01 | List constructors, `[a,b,c]` notation | 1 (`rfl`) | Fine: warmup |
| L02 | `rw` with `List.length_cons` | 1 (`rw`) | Fine: first-contact for rw-with-API pattern |
| L03 | Membership via `List.mem_cons`, `left`/`right` | 3 | Good: clean first-contact |
| L04 | Membership in append via `List.mem_append` | 3 | Good: transfers L03 pattern |
| L05 | Map preserves membership, `refine` | 3 | Good: new proof pattern (existential) |
| L06 | Filter membership, `constructor` for `∧` | 4 | Good: new proof pattern (conjunction) |
| L07 | `rw` with `List.length_append` | 1 | Thin but justified as retrieval |
| L08 | `List.get` and Fin-indexing connection | 1 (`rfl`) | Thin but conceptually important |
| L09 | `List.Nodup`, recursive unfolding, `simp` introduction | ~8 | Good: appropriate for concept + new tactic |
| L10 | Retrieval: combining `mem_cons` + `mem_append` | 5 | Good: no new material, tests integration |
| L11 | Boss: integrating filter + map + constructor + refine | 7 | Good: genuine integration with planning |

### 7b. Center of gravity

Stable: **list API lemma-based reasoning via `rw`**, with progressive introduction of logical structure tactics (`left`/`right`, `constructor`, `refine`).

### 7c. Difficulty progression (unchanged)

```
L01 [*------] warmup (1 step, rfl)
L02 [**-----] first rw (1 step, symbolic)
L03 [***----] first multi-step (3 steps, new: left/right)
L04 [***----] same pattern, new lemma (3 steps)
L05 [****---] new pattern: existential (3 steps, new: refine)
L06 [****---] new pattern: conjunction (4 steps, new: constructor)
L07 [**-----] retrieval (1 step, easy rw)
L08 [**-----] concept bridge (1 step, rfl)
L09 [******-] longest, recursive unfolding + simp (8 steps)
L10 [*****--] retrieval, combining 2 lemmas (5 steps)
L11 [*******] boss, all skills (7 steps)
```

Broadly good. The L07-L08 dip before the L09-L11 climb is intentional (breather).

---

## 8. Learner Simulation

### 8a. Attentive Novice (post-R3 gating)

**Profile**: Completed NNG4. New to lists.

**Experience with gated world**:

1. **L01**: `rfl`. Quick warmup. Notation established. (5 seconds.)

2. **L02**: Sees `(0 :: l).length = l.length + 1`. Cannot use `simp` (disabled). Cannot use `decide` (disabled). Reads about `List.length_cons`. Types `rw [List.length_cons]`. Success. **Learns the core pattern**: find the right API lemma, rewrite with it. (1 minute.)

3. **L03**: Sees `5 ∈ 5 :: l`. Cannot use `simp` or `decide`. Must engage structurally. Reads about `List.mem_cons`. Types `rw [List.mem_cons]`. Sees `5 = 5 ∨ 5 ∈ l`. Learns `left`/`right`. Types `left`, then `rfl`. **Key learning moment**: disjunctions in proofs. (2 minutes.)

4. **L04**: Pattern recognition from L03. Types `rw [List.mem_append]`, `left`, `exact h`. Smooth transfer. (1 minute.)

5. **L05**: Existential goal. New: `refine`. **First likely stuck point**: the learner sees `∃ a_1 ∈ l, f a_1 = f a` and must figure out how to provide a witness. The hint guides them to `refine ⟨a, h, ?_⟩`. The angle-bracket syntax is a burden, but the hint is explicit. (3 minutes.)

   **Most likely wrong move**: Trying `use a` (which may work but is not the guided path -- no `Branch` covers this). Or trying `exact a` (wrong -- `a` is not the proof). Hint rescues by showing `refine` syntax.

6. **L06**: Conjunction goal. `constructor` should be familiar from NNG4. Smooth. (2 minutes.)

7. **L07**: Single `rw [List.length_append]`. Quick retrieval. (30 seconds.)

8. **L08**: `rfl` on concrete `List.get`. Reads the conceptual connection to Fin from W1. Quick. (30 seconds.)

9. **L09**: The longest level. The novice encounters `Nodup` for the first time. **Second likely stuck point**: after the first `rw [List.nodup_cons]` + `constructor`, the learner must handle the focused subgoal syntax (`·`). If they have not seen `·` before, they may be confused. The hint says "try `simp`" for the non-membership goal, which works. The iterative pattern (unfold, split, evaluate, repeat) is new and takes time to internalize. (5-7 minutes.)

   **Risk**: The learner types bare `simp` at the top and the level closes immediately. They miss the `nodup_cons` pattern. **Mitigation**: The introduction explicitly walks through the step-by-step approach and says "use `simp` for the concrete non-membership checks." A conscientious learner who reads the introduction will follow the guided path. A learner who shortcuts with `simp` has at least seen the explanation and used the tactic being taught.

10. **L10**: Combining `mem_cons` + `mem_append`. The novice must navigate two layers of disjunction. With hints, manageable. Without hints, a genuine challenge. **Good retrieval exercise.** (3 minutes.)

11. **L11 (Boss)**: Multi-layer proof: filter -> map -> conjunction + existential. The novice must plan. With hints at each step, they should succeed. The planning challenge is real: "which layer do I peel first?" **Can the novice explain the proof afterward?** Yes: "To show f(a) is in the filtered mapped list, I need it to be in the mapped list AND satisfy the predicate. It's in the mapped list because a is in the original list." (5 minutes.)

**Overall novice experience**: 20-30 minutes. Genuine proof skills acquired. The gating ensures every step requires engagement.

**What the novice learns**:
- Using `rw` with API lemmas to unfold definitions
- Navigating disjunctions with `left`/`right`
- Splitting conjunctions with `constructor`
- Providing existential witnesses with `refine`
- Recursive unfolding pattern for `Nodup`
- Integrating multiple proof steps in a single argument

### 8b. Experienced Lean User (post-R3 gating)

**Profile**: Comfortable with Lean 4. Has used lists before.

**Experience**:
1. L01: `rfl`. Quick.
2. L02: `simp` disabled. Must use `rw [List.length_cons]`. Slightly annoying but teaches the pattern. (May try `exact List.length_cons 0 l` -- which is not a bypass but a different style.)
3. L03-L06: `simp` and `aesop` disabled. May use library one-liners (`exact List.mem_cons_self`, etc.) -- these work and skip the guided path. **This is the remaining expert bypass.** However, these require knowing exact Mathlib API names, which is itself a form of knowledge. A learner who knows `List.mem_cons_self` already understands what the level teaches.
4. L07: `simp` disabled. `rw [List.length_append]`. Quick.
5. L08: `rfl`. Quick.
6. L09: `simp` available. Expert may type bare `simp`. One step. Misses `nodup_cons` pattern but learns `simp` can handle concrete `Nodup` checks.
7. L10-L11: `simp`/`aesop` disabled. Must engage structurally unless they know library lemmas. Library one-liners still work for L10 (`List.mem_cons_of_mem`) and L11 (`List.mem_filter.mpr`).

**Assessment**: The experienced user can still bypass most levels via library one-liners, but this requires genuine Mathlib API knowledge. The `aesop` universal bypass is gone. The tactic gating forces at minimum a search-tactic query (`exact?`) or library lookup, which is more engagement than zero. Acceptable for a lecture world.

**Avoidable friction**: None problematic. The expert who wants to speed through can, but must demonstrate API knowledge to do so.

---

## 9. Boss Integrity (L11)

### Boss: "Map, filter, and membership"

**Statement**: Given `a ∈ l` and `p (f a) = true`, prove `f a ∈ List.filter p (List.map f l)`.

**Post-gating exploitability**:
- `decide`: Disabled
- `simp`: Disabled
- `aesop`: **Disabled**
- Library one-liner: `exact List.mem_filter.mpr ⟨List.mem_map_of_mem f h, hp⟩` -- works (P2)

**With `aesop` now disabled, the boss requires genuine engagement** (unless the learner knows the exact library shortcut). The 7-step guided proof exercises 4 distinct skills from earlier levels.

**Seeded subskills check** (unchanged, still all pass):
- [x] `rw [List.mem_filter]` -- taught in L06
- [x] `constructor` for `∧` -- taught in L06, reinforced in L09
- [x] `rw [List.mem_map]` -- taught in L05
- [x] `refine ⟨..., ?_⟩` -- taught in L05
- [x] `rfl` -- baseline
- [x] `exact` with hypothesis -- used throughout

**Closure quality**: PASS. Every subskill has been introduced and practiced.
**Integration quality**: PASS. Requires planning (filter layer, then map layer).
**Surprise burden**: PASS. 7 steps; similar length to L09 but different structure.
**Explanation test**: PASS. Learner can articulate the proof in natural language.

**Boss verdict**: Genuine integration boss. PASS.

---

## 10. Course-Role Sanity

The world functions as a **Lecture** world. All lecture requirements are met:

| Requirement | Status |
|-------------|--------|
| Introduces new concepts (text + proof) | PASS |
| First-contact with new proof moves | PASS: `rw`-with-API, `left`/`right`, `constructor`, `refine`, `simp` |
| Worked examples with visible proof structure | PASS: L02-L06 are structured worked examples |
| Builds toward integrative boss | PASS: L11 integrates 4+ skills |
| Practice levels for mastery | PASS: L07-L08 (retrieval), L10 (combination) |
| Transfer moments | PASS: "In plain language" in every conclusion |

---

## 11. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| Library one-liner bypasses (no `DisabledTheorem`) | P2 | L03-L06, L10, L11 can be solved by a single `exact` with the right library lemma. Low-probability exploit for target audience. |
| L09 `simp` exploit | P2 | Bare `simp` closes the 8-step Nodup proof. Deliberate choice (level teaches `simp`). |
| Focused subgoal syntax (`·`) undocumented | P2 | Used in guided proofs for L06, L09, L11. No `TacticDoc`. |
| No `Branch` for alternative tactic paths | P2 | Learners trying `use` (L05), `Or.inl` (L03), `And.intro` (L06) get no guidance. |
| No counterexample level for `Nodup` | P2 | `[1,2,1]` failing `Nodup` is only discussed verbally in L09 conclusion. |
| `import Mathlib` in every file | P2 | Heavyweight but consistent with project convention. |
| Auto-generated variable name `a_1` in L05 goal | P3 | After `rw [List.mem_map]`, the goal shows `∃ a_1 ∈ l, f a_1 = f a`. The `a_1` name is auto-generated because `a` is already in scope. Hint explains the goal, so not confusing. |

---

## 12. Ranked Patch List

### P0 (Blocking)

None. All P0 issues from R1 and R2 are resolved.

### P1 (High -- should fix)

None. The R2 P1 issues (`simp` on L02/L07) are resolved. The L09 `simp` situation is accepted as P2.

### P2 (Medium -- nice to fix, non-blocking)

1. **Add `DisabledTheorem` for shortcut lemmas on relevant levels.** Specifically:
   - L03: `DisabledTheorem List.mem_cons_self`
   - L04: `DisabledTheorem List.mem_append_left List.mem_append_right`
   - L05: `DisabledTheorem List.mem_map_of_mem`
   - L10: `DisabledTheorem List.mem_cons_of_mem List.mem_append_right`
   - L11: `DisabledTheorem List.mem_map_of_mem` (already blocked by L05 if cumulative, but verify)

2. **Document the focused subgoal syntax (`·`).** Add a brief `TacticDoc` or mention in L06's introduction where `·` first appears in the guided proof. Even a single sentence ("Use `·` to focus on a specific subgoal after `constructor`") would help.

3. **Add a `Branch` in L05 for learners who try `use`.** After `rw [List.mem_map]`, a `Branch` catching `use a` and guiding from there would improve recoverability. Similarly, a `Branch` in L03 for `exact List.mem_cons_self 5 l` could redirect to the intended path.

4. **Consider adding a `Nodup` counterexample level** (e.g., L09b proving `¬ [1, 2, 1].Nodup` or showing that the first `rw [List.nodup_cons]` produces a false subgoal). This would be a strong conceptual complement to L09. Would require renumbering L10-L11.

5. **Strengthen L07.** Consider a statement like `(l₁ ++ l₂ ++ l₃).length = l₁.length + l₂.length + l₃.length` requiring two rewrites (`rw [List.length_append, List.length_append]`) to distinguish it from L02's single-rewrite pattern and give the learner a multi-rewrite exercise.

### P3 (Low -- polish items)

6. **Improve L05 introduction emphasis on step-by-step approach.** The introduction presents both `refine ⟨a, h, ?_⟩` (step-by-step) and `exact ⟨a, h, rfl⟩` (one-shot) as alternatives. Recommend leading more strongly with the step-by-step approach and presenting the one-shot as a "once you're comfortable" alternative.

7. **Consider adding `norm_num` to L01/L08 `DisabledTactic`** for consistency, even though neither level is exploitable by it.

---

## 13. What to Playtest Again After Patching

If the P2 patches above are implemented:

1. **Any level with new `DisabledTheorem`**: Verify the intended proof still works (it should -- `DisabledTheorem` only blocks `exact that_lemma`, not `rw [that_lemma]`).
2. **Any level with new `Branch`**: Verify the branch proof compiles and the hint fires in the right state.
3. **A new Nodup counterexample level** (if added): Full first-audit treatment.
4. **L07 if strengthened**: Verify the multi-rewrite proof works and hints guide correctly.

None of these require a full re-audit. A targeted check would suffice.

---

## 14. Summary of Defects by Taxonomy

| Taxonomy # | Defect | Where | R1 | R2 | R3 |
|-----------|--------|-------|----|----|-----|
| #8 Fake boss | Boss closable by single tactic | L11 | P0 (decide) | P0 (aesop) | **Resolved** |
| #3 Overfine | Identical proof shape across levels | All | P1 | Resolved | Resolved |
| #4 Surface coverage only | API items never practiced structurally | All | P0 | Resolved | Resolved |
| #6 Spoiler hint | Every hint gives exact tactic | All | P1 | Resolved | Resolved |
| #12 Syntax dominates math | Learner learns API names, not proof moves | All | P0 | Resolved | Resolved |
| #13 Expert hostility | Universal bypass via single tactic | All | P0 (decide) | P1 (aesop) | P2 (library one-liners only) |

---

## 15. Final Assessment

The W3 ListBasics world has successfully resolved all blocking defects across three audit rounds:

- **R1** found a completely hollow world with zero proof structure. All statements were concrete decidable propositions closable by `decide`.
- **R2** found a dramatically re-authored world with genuine proof structure, but the `aesop` tactic was ungated, providing a universal bypass.
- **R3** confirms that `aesop` is now disabled on all 11 levels, `simp` is disabled on L02 and L07 (the two levels where it was an unintended bypass), and the remaining `simp` availability on L09 is a deliberate pedagogical choice.

The world now teaches real proof patterns (API-lemma rewriting, disjunction navigation, conjunction splitting, existential witnesses), has a genuine integration boss, covers the `Nodup` bridge to W4, and cannot be trivially bypassed by any single tactic.

**Remaining items are P2 polish**: library lemma one-liners (fixable via `DisabledTheorem`), focused-subgoal syntax documentation, alternative-path `Branch` coverage, and a potential `Nodup` counterexample level. None are blocking.

**Verdict: PASS.** The world is shippable.
