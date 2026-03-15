# Playtest Audit (Round 4): W3 ListBasics

**Auditor**: playtest-auditor (adversarial)
**World**: W3 -- Lists: construction and operations
**World type**: Lecture
**Levels audited**: L01 through L11 (11 levels)
**Build status**: Compiles (verified via `lake env lean`)
**Prior audits**: R1 (FAILING), R2 (CONDITIONAL PASS), R3 (PASS, 3.3 rubric)

**Changes since R3**: Enrichment R4 implemented three items:
1. L09 statement changed to `([1, 2, 3] : List Nat).Nodup /\ (1 : Nat) in [2, 1]`
2. L09 introduction now has a dedicated `simp` explanation section
3. L10 completely rewritten: teaches backward reasoning with `rw [...] at h` and `rcases`
4. L10 adds `NewTactic rcases` with `TacticDoc`

---

## 0. Prior Issue Resolution and Delta Analysis

### What changed since R3

| Change | File | Nature of change |
|--------|------|-----------------|
| L09 statement expanded to conjunction | L09_Nodup.lean | Statement now includes `(1 : Nat) in [2, 1]` as second conjunct |
| L09 intro expanded | L09_Nodup.lean | New "The `simp` tactic" section explains simp before use |
| L10 completely rewritten | L10_Practice.lean | Was forward-only membership; now teaches `rw [...] at h` + `rcases` |
| `rcases` TacticDoc added | L10_Practice.lean | Proper documentation for `rcases` |

### R3 Issues Status

| R3 # | R3 Issue | Severity | Status in R4 | Detail |
|-------|----------|----------|-------------|--------|
| R3 P2-1 | No `DisabledTheorem` for shortcut lemmas | P2 | **Unchanged** | Still no `DisabledTheorem` on L03-L06, L10, L11. Not addressed in enrichment. |
| R3 P2-2 | Focused subgoal syntax undocumented | P2 | **Unchanged** | `cdot` still undocumented. |
| R3 P2-3 | No `Branch` for alternative paths | P2 | **Unchanged** | No `Branch` added for `use` in L05, `Or.inl` in L03, etc. |
| R3 P2-4 | No Nodup counterexample level | P2 | **Partially addressed** | L09 now includes `1 in [2, 1]` as a second conjunct, demonstrating the membership that blocks `[1,2,1].Nodup`. Not a separate level but the concept is exercised. |
| R3 P2-5 | L07 could be strengthened | P2 | **Unchanged** | Still a single-rewrite level. |
| R3 P2 (L09 simp) | `simp` closes L09 in one step | P2 | **Still present** | `simp` closes the new conjunction `([1,2,3] : List Nat).Nodup /\ (1 : Nat) in [2, 1]` in one step. Confirmed by testing. |

---

## 1. Technical Sanity

### 1a. Build and imports

All 11 level files compile. The world base file (`Game/Levels/ListBasics.lean`) imports all 11 levels in order. No import issues detected.

### 1b. Statement Exploitability

This is the primary focus of R4 given the L09 and L10 changes.

#### L09 (New conjunction statement)

**Statement**: `([1, 2, 3] : List Nat).Nodup /\ (1 : Nat) in [2, 1]`

**Disabled**: `decide`, `native_decide`, `simp_all`, `aesop`
**Available**: `simp`, `norm_num`

**Exploit test results**:

| Tactic | Closes entire statement? | Tested |
|--------|-------------------------|--------|
| `simp` | **YES** -- one step | Confirmed |
| `norm_num` | **YES** -- one step | Confirmed |
| `constructor <;> simp` | YES -- two steps | Confirmed |
| `decide` | Disabled | N/A |
| `aesop` | Disabled | N/A |

**Assessment**: The new conjunction does NOT improve exploit resistance. Both `simp` and `norm_num` close the entire statement (including the new `1 in [2, 1]` conjunct) in a single step. The enrichment change adds pedagogical value (the learner sees both a Nodup success and a membership that blocks a different Nodup) but does not change the exploitability profile.

**Severity**: P2 (unchanged from R3). This remains a deliberate pedagogical trade-off. L09 introduces `simp` via `NewTactic simp`. The intended proof uses `simp` for the non-membership subgoals. Disabling `simp` would require a replacement mechanism for evaluating concrete membership propositions, and `decide` is already disabled. The R3 analysis of this trade-off remains valid.

**New concern: `norm_num` exploit**. `norm_num` is available and not disabled on L09, and it closes the entire statement. This was not noted in R3 because R3's statement was `[1, 2, 3].Nodup` alone, and I did not test `norm_num` on it. With `norm_num` also closing the new statement, there are now two available automation tactics that bypass the entire level.

However, `norm_num` is not introduced as a `NewTactic` in this world (it was introduced in W2 for numeric computations). A learner who discovers that `norm_num` closes a list-Nodup+membership goal has transferred a tactic to a surprising context, which is itself a form of learning. Still, this is worth noting.

**P2 recommendation**: Add `norm_num` to L09's `DisabledTactic`. This does not affect the `simp` trade-off (which remains deliberate) but closes a secondary exploit vector. The intended proof never uses `norm_num`.

#### L10 (New backward reasoning statement)

**Statement**: `a in l1 ++ l2 -> a in l2 ++ l1` (with hypothesis `h : a in l1 ++ l2`)

**Disabled**: `decide`, `native_decide`, `simp`, `aesop`

**Exploit test results**:

| Tactic/Path | Closes statement? | Bypasses lesson? |
|------------|-------------------|-----------------|
| `simp` | Disabled | N/A |
| `exact List.mem_append.mpr (List.mem_append.mp h \|>.symm)` | YES | YES -- library one-liner |
| `rw [List.mem_append] at h; rw [List.mem_append]; exact Or.comm.mp h` | YES | Partially -- uses `rw at h` (intended) but skips `rcases` |
| `simp only [List.mem_append] at h \|-, exact Or.comm.mp h` | Would work if `simp` were available | N/A |

**Assessment**: The level is well-gated against automation exploits. The library one-liner requires knowing `List.mem_append.mp` and `Or.Symm`, which is genuine API knowledge. The `Or.comm.mp` shortcut requires the learner to at least use `rw [...] at h` (one of the two new skills), just skipping `rcases`. Neither of these is realistic for the target audience.

**Severity**: P2 (library one-liners, same as other levels). No new P0 or P1 issues.

#### L11 (Boss -- unchanged)

No changes to L11. All R3 findings remain valid. `simp` and `aesop` are disabled. The library one-liner `exact List.mem_filter.mpr (List.mem_map_of_mem f h, hp)` works but requires expert-level API knowledge. P2.

**Boss does not exercise `rcases`**: This was noted by the enrichment reviewer (observation #3) and is the key question for this audit round. See Section 4 (Coverage) for detailed analysis.

#### Full level-by-level gating summary (R4)

| Level | `decide` | `native_decide` | `simp` | `simp_all` | `aesop` | Remaining exploit |
|-------|----------|-----------------|--------|------------|---------|-------------------|
| L01 | D | D | -- | -- | D | None (`rfl`) |
| L02 | D | D | D | -- | D | None |
| L03 | D | D | D | -- | D | Library one-liner (P2) |
| L04 | D | D | D | -- | D | Library one-liner (P2) |
| L05 | D | D | D | -- | D | Library one-liner (P2) |
| L06 | D | D | D | -- | D | Library one-liner (P2) |
| L07 | D | D | D | -- | D | None |
| L08 | D | D | -- | -- | D | None (`rfl`) |
| L09 | D | D | -- | D | D | `simp` (P2, deliberate), `norm_num` (P2, new) |
| L10 | D | D | D | -- | D | Library one-liner (P2) |
| L11 | D | D | D | -- | D | Library one-liner (P2) |

### 1c. Interactive Proof Quality

#### L09 (expanded)

The L09 proof is now longer due to the second conjunct. After `constructor`:

- First branch: 8 steps (unchanged Nodup proof)
- Second branch: 4 steps (`rw [List.mem_cons]`, `right`, `rw [List.mem_cons]`, `left`, `rfl`)

Every step produces a visible goal-state change. The focused-subgoal syntax (`cdot`) separates branches clearly. No elaborate one-liners. PASS.

#### L10 (rewritten)

The L10 proof has 8 tactic steps across two branches:
1. `rw [List.mem_append] at h` -- visible hypothesis change
2. `rcases h with h1 | h2` -- splits into two subgoals (visible)
3. Branch 1: `rw [List.mem_append]`, `right`, `exact h1` (3 steps, each visible)
4. Branch 2: `rw [List.mem_append]`, `left`, `exact h2` (3 steps, each visible)

Each step is short and produces clear feedback. The `rcases` step is the most complex (new syntax `h1 | h2`) but is well-hinted. PASS.

No red flags for elaborate one-liners, opaque goals, or missing feedback anywhere in the world.

---

## 2. Coverage Sanity

### 2a. Coverage item status (updated for R4 changes)

| Item | Axis | Coverage States | Change from R3 |
|------|------|----------------|----------------|
| M16 (List basic API) | MATH | I (L01), S (L02-L07), G (L11) | No change |
| M17 (List.Nodup) | MATH | I (L09), including failure case | **Improved**: now exercises both success and failure |
| N11 (`::` notation) | NOTATION | I (L01), S (L02, L03) | No change |
| N12 (`++` notation) | NOTATION | I (L04), S (L07, L10) | No change |
| V1 (unfolding definitions via `rw`) | MOVE | Practiced in L02-L07, L09-L11 | No change |
| V-left/right | MOVE | I (L03), S (L04, L09, L10) | **Improved**: L10 uses `left`/`right` after `rcases` |
| V-constructor | MOVE | I (L06), S (L09, L11) | No change |
| V-refine | MOVE | I (L05), S (L11) | No change |
| `rw [...] at h` | MOVE | **I (L10)** | **NEW**: backward rewriting introduced |
| `rcases` | LEAN | **I (L10)** | **NEW**: case-splitting tactic introduced |
| `simp` | LEAN | I (L09) | No change |

### 2b. Coverage gaps

#### Gap 1: `rcases` not tested in boss -- is this a P1?

This is the central question the prompt asks about. Let me analyze it carefully.

**The case that this IS a problem**:
- `rcases` is introduced in L10, the level immediately before the boss.
- The boss (L11) does not use `rcases` at all. It uses only forward reasoning: rewrite the goal, split with `constructor`, provide a witness.
- By the closure-before-boss principle (reference 05, section 7), a boss subskill should have been "introduced AND practiced before the boss." Here, `rcases` is introduced but never tested in the boss. This is not the same as a boss depending on an untaught skill -- it is a boss that ignores a recently taught skill.
- From the failure taxonomy (reference 04, #8 "fake boss" and #8b "gauntlet boss"): the boss integrates L03-L06 skills but not L10 skills. It is a genuine integration of four skills, not a gauntlet, but it does have a blind spot.

**The case that this is NOT a problem**:
- `rcases` is a general-purpose tactic. Its real testing ground is downstream worlds (W4, W6-W8) where membership hypotheses need destructuring constantly. L10 is a preview/seed, not the main use.
- The boss is not *supposed to* exercise every skill in the world. It integrates the world's "main" skills (API-lemma rewriting, disjunction/conjunction navigation, existential witnesses). Backward reasoning is a supplementary skill.
- Adding `rcases` to the boss would require redesigning the boss statement to include a hypothesis that needs destructuring, which changes the boss's character.
- The plan (W3 section) says the boss should "combine `map`, `filter`, `length`, and membership in one proof" -- it does not mention backward reasoning.

**Verdict**: P2. The gap is real but not blocking. The boss integrates the world's core repertoire (forward membership reasoning with API lemmas). `rcases` is seeded in L10 and will be heavily used in downstream worlds. The boss's omission of `rcases` means the learner does not get reinforcement on this specific skill before leaving the world, but the skill is a single-level introduction, not the world's main theme.

However: if a future audit finds that learners struggle with `rcases` in W4 or W6, the root cause may trace back here. This is a documented risk.

#### Gap 2: `rw [...] at h` not tested in boss

Same analysis as `rcases`. The boss uses `rw` only on the goal, never on a hypothesis. P2 for the same reasons.

#### Gap 3: No `DisabledTheorem` (carried from R3)

P2, unchanged. Library one-liners bypass L03-L06, L10, L11.

#### Gap 4: Focused subgoal syntax undocumented (carried from R3)

P2, unchanged.

### 2c. New coverage provided by R4 changes

The R4 changes significantly improve two coverage areas:

1. **Nodup failure case (L09)**: The learner now proves `1 in [2, 1]` themselves and the conclusion explains why this blocks `[1, 2, 1].Nodup`. This satisfies the plan requirement ("Prove a specific list has no duplicates, and show one that does") and the R3 P2-4 item. Good.

2. **Backward membership reasoning (L10)**: `rw [...] at h` and `rcases` are the dominant proof pattern for downstream finset worlds. Their introduction here is the single most important improvement across all four audit rounds. The learner now has forward AND backward membership reasoning before entering W4/W5.

---

## 3. Granularity Sanity

### 3a. Level-by-level review

| Level | Dominant Lesson | Steps | R3 Verdict | R4 Verdict |
|-------|----------------|-------|------------|------------|
| L01 | List constructors | 1 | Fine | Fine |
| L02 | `rw [List.length_cons]` | 1 | Fine | Fine |
| L03 | Membership + `left`/`right` | 3 | Good | Good |
| L04 | Membership in append | 3 | Good | Good |
| L05 | Map + `refine` | 3 | Good | Good |
| L06 | Filter + `constructor` | 4 | Good | Good |
| L07 | `rw [List.length_append]` | 1 | Thin but justified | Thin but justified |
| L08 | Fin-indexing connection | 1 | Thin but justified | Thin but justified |
| L09 | Nodup + `simp` + failure case | ~12 | Good (8 steps) | **Good but larger** (~12 steps including part 2) |
| L10 | Backward reasoning + `rcases` | 8 | Was "retrieval" | **Significantly changed**: now first-contact for two new skills |
| L11 | Boss: map + filter integration | 7 | Good | Good (but see coverage gap re `rcases`) |

### 3b. L09 granularity concern

L09 now teaches THREE things:
1. `List.Nodup` and the `nodup_cons` recursive unfolding pattern
2. `simp` as a tactic (first introduction via `NewTactic simp`)
3. Nodup failure demonstration (`1 in [2, 1]`)

This is at the edge of the novelty budget. The plan says "each level should introduce at most one truly new burden." However:
- `Nodup` and the `nodup_cons` pattern are tightly coupled (one definition, one unfolding lemma)
- `simp` is introduced as a tool specifically for the subgoals created by the `Nodup` proof (non-membership checks)
- The failure case demonstration (`1 in [2, 1]`) reuses skills from L03 (`rw [List.mem_cons]`, `left`/`right`, `rfl`)

The three burdens are interleaved (Nodup needs simp needs membership), not independent. This is acceptable. The level is long (~12 steps) but not overbroad because every step serves the same conceptual purpose: understanding what `Nodup` means.

**Verdict**: Acceptable. Not a defect.

### 3c. L10 granularity concern

L10 now introduces TWO new skills simultaneously:
1. `rw [...] at h` (rewriting hypotheses instead of goals)
2. `rcases h with h1 | h2` (case-splitting on disjunctions)

Both are introduced in the same level. This is a genuine novelty-budget concern. However:
- `rw` on goals is already well-practiced (L02-L07, L09). The `at h` modifier is a small extension, not a new concept.
- `rcases` for disjunctions is the natural follow-up once you have a disjunction in a hypothesis. The learner has already used `left`/`right` to construct disjunctions; `rcases` destructures them.
- The proof structure is symmetric: after `rcases`, both branches are identical in shape (rewrite goal, choose branch, exact). This symmetry reinforces the skill immediately.
- The hints guide every step explicitly.

**Verdict**: Acceptable. The two skills are complementary (get a disjunction via `rw at`, then split it via `rcases`) and would be pedagogically weaker if separated. The combined introduction creates a complete "backward reasoning" lesson.

### 3d. Center of gravity

Stable and unchanged: **list API lemma-based reasoning via `rw`**, with progressive introduction of logical structure tactics. L10's addition of backward reasoning enriches the center of gravity without destabilizing it.

### 3e. Difficulty progression (updated for R4)

```
L01 [*------] warmup (1 step, rfl)
L02 [**-----] first rw (1 step, symbolic)
L03 [***----] first multi-step (3 steps, new: left/right)
L04 [***----] same pattern, new lemma (3 steps)
L05 [****---] new pattern: existential (3 steps, new: refine)
L06 [****---] new pattern: conjunction (4 steps, new: constructor)
L07 [**-----] retrieval (1 step, easy rw)
L08 [**-----] concept bridge (1 step, rfl)
L09 [*******] longest, Nodup + simp + failure case (~12 steps)
L10 [******-] NEW: backward reasoning, 2 new skills (8 steps)
L11 [*******] boss, integrates L03-L06 skills (7 steps)
```

The difficulty curve is appropriate. L07-L08 provide a breather before the L09-L11 climb. The peak at L09 (longest level) is followed by L10 (moderate difficulty but new skills) and L11 (boss, similar length but retrieval of familiar skills).

---

## 4. Learner Simulation

### 4a. Attentive Novice

**Profile**: Completed NNG4. New to lists. Following the R4 world.

**L09 experience (new conjunction)**:

The novice reaches L09 after 8 levels of building membership proofs. They see a conjunction goal. The introduction explains `Nodup`, `nodup_cons`, and introduces `simp` with a dedicated section.

1. Types `constructor` to split the conjunction. Two branches appear.
2. **Branch 1** (`[1,2,3].Nodup`): Follows the guided unfolding. `rw [List.nodup_cons]`, `constructor`, `simp` for non-membership, repeat. The `nodup_nil` base case is satisfying. (5 minutes.)
3. **Branch 2** (`1 in [2, 1]`): Recognizes the membership pattern from L03. Types `rw [List.mem_cons]`, `right`, `rw [List.mem_cons]`, `left`, `rfl`. (2 minutes.)
4. Reads the conclusion connecting the two: "you just proved 1 is in [2, 1], which is why [1, 2, 1] fails Nodup." **This is a good learning moment.**

**Risk**: The novice types `simp` at the top before `constructor`. The entire level closes. They miss everything. **Mitigation**: The introduction says "Strategy for part 1: `constructor` to split the conjunction" before mentioning `simp`, and the first hint says "The goal is a conjunction. Split it with `constructor`." A hint-reading novice will follow the guided path.

**L10 experience (new backward reasoning)**:

The novice sees `h : a in l1 ++ l2` in the context and `a in l2 ++ l1` as the goal.

1. Reads the introduction explaining `rw [...] at h` and `rcases`. Two new concepts, but the introduction treats them as tools for one job (analyzing a hypothesis).
2. **First likely stuck point**: The novice may try `rw [List.mem_append]` (on the goal) first, getting `a in l2 \/ a in l1`. This changes the goal but does not help because they still have `h : a in l1 ++ l2` untouched. The hint fires: "Rewrite **the hypothesis** (not the goal)."
3. Types `rw [List.mem_append] at h`. Sees `h : a in l1 \/ a in l2`. New experience: the hypothesis changed.
4. **Second likely stuck point**: The novice may try `left` or `right` on the goal (which is still `a in l2 ++ l1`, not a disjunction). Hint fires: "split into two cases with `rcases h with h1 | h2`."
5. Types `rcases h with h1 | h2`. Two subgoals appear. **Key moment**: the novice sees that case analysis on a hypothesis creates branches, just like `cases` in NNG4.
6. Each branch follows the familiar forward pattern: `rw [List.mem_append]`, choose branch, `exact`. (3 minutes per branch.)

**Can the novice explain the proof afterward?** Yes: "If a is in l1++l2, then it's either in l1 or l2. If it's in l1, then it's in l2++l1 (right side). If it's in l2, then it's in l2++l1 (left side)."

**L11 experience (boss, unchanged)**:

The novice reaches the boss with all the skills it requires. The boss uses only forward reasoning (from L03-L06). The novice does not need `rcases` or `rw at`. This is fine -- the boss tests the world's primary skills, and the novice has those.

**Would the novice notice that `rcases` is unused?** Probably not. The boss is challenging enough (7 steps, planning required) that the novice is focused on integrating filter+map+membership, not on checking which tactics are missing.

### 4b. Experienced Lean User

**Profile**: Comfortable with Lean 4.

**L09**: May type bare `simp` and close in one step. Or `norm_num`. Misses the `nodup_cons` pattern but learns that automation can handle concrete list properties. Acceptable -- the experienced user already knows how recursive definitions work.

**L10**: The experienced user may recognize `List.mem_append_comm` or use `Or.comm.mp` after a `simp only` rewrite. These shortcuts require genuine API knowledge and still exercise at least part of the intended skills. The `rw [...] at h` pattern is valuable even for experienced users who have not seen it before.

**L11**: May use `exact List.mem_filter.mpr (List.mem_map_of_mem f h, hp)`. This requires knowing three API lemmas by name. P2.

**Avoidable friction**: None new. The experienced user's path through R4 is smoother than R3 because L10 now teaches a genuinely useful skill (`rw at`, `rcases`) rather than being a forward-only retrieval exercise.

---

## 5. Boss Integrity (L11)

### Seeded subskills check

| Subskill | Where seeded | Used in boss? |
|----------|-------------|--------------|
| `rw [List.mem_filter]` | L06 (I) | YES |
| `constructor` for `/\` | L06 (I), L09 (S) | YES |
| `rw [List.mem_map]` | L05 (I) | YES |
| `refine <..., ?_>` | L05 (I) | YES |
| `rfl` | Baseline | YES |
| `exact` with hypothesis | Throughout | YES |
| `rw [...] at h` | L10 (I) | **NO** |
| `rcases` | L10 (I) | **NO** |

**Closure quality**: PASS for the skills the boss uses. All six boss subskills have been introduced and practiced.

**Integration quality**: PASS. The boss requires planning across two layers (filter and map) and combines four operations.

**Surprise burden**: PASS. No new skill required. 7 steps; length comparable to L09/L10.

**Coverage completeness**: Partial. The boss does not integrate L10's new skills (`rw at`, `rcases`). This is the coverage gap identified in Section 2b. The boss tests 6 of 8 world skills. The missing skills are the newest additions.

**Is this an automatic red flag?** The rubric says "a boss that depends on an untaught micro-skill" is a red flag. The converse -- a boss that does not depend on a taught skill -- is not listed as an automatic red flag. It is a coverage gap, not a structural defect.

**Boss verdict**: PASS. The boss is a genuine integration boss for the world's primary skill family. The `rcases`/`rw at` gap is noted as P2.

---

## 6. Course-Role Sanity

The world continues to function as a **Lecture** world. The R4 changes strengthen its lecture role:

| Requirement | Status | R4 Impact |
|-------------|--------|-----------|
| Introduces new concepts | PASS | L09 now covers success AND failure of Nodup |
| First-contact with proof moves | PASS | L10 now provides first-contact for backward reasoning |
| Worked examples | PASS | L02-L06 unchanged |
| Builds toward boss | PASS | L11 unchanged |
| Practice for mastery | PASS | L10 now provides real practice, not just retrieval |
| Transfer moments | PASS | Unchanged |

L10's role has changed from "retrieval exercise" to "first-contact level for backward reasoning." This is appropriate for its position (penultimate level, after all forward skills are established). It meets the first-contact requirements:
- The mathematics is familiar (append membership, well-practiced since L04)
- The new moves (`rw at`, `rcases`) are documented with TacticDoc
- There is a rescue path (hints at every step)

---

## 7. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| `norm_num` closes L09 in one step | P2 (new) | `norm_num` is available and not disabled on L09. Closes the entire conjunction. Secondary exploit vector alongside `simp`. |
| `simp` closes L09 in one step | P2 (known) | Unchanged from R3. Deliberate trade-off. |
| Library one-liner bypasses | P2 (carried) | L03-L06, L10, L11 closable by expert one-liners. |
| `rcases` not exercised in boss | P2 (new) | See coverage gap analysis. |
| `rw [...] at h` not exercised in boss | P2 (new) | Same analysis. |
| Focused subgoal syntax undocumented | P2 (carried) | Used in L06, L09, L11. |
| No `Branch` for alternative paths | P2 (carried) | L05 (`use`), L03 (`Or.inl`), etc. |
| `import Mathlib` heavyweight | P2 (carried) | Consistent with project convention. |

---

## 8. Rubric Scores

| Category | R3 | R4 | Notes |
|----------|----|----|-------|
| 1. Coverage closure | 3 | 3+ | Improved: Nodup failure case exercised, backward reasoning added. Still missing `rcases` in boss. |
| 2. Granularity fit | 3 | 3 | L09 slightly heavier but coherent. L10 has 2 new burdens but complementary. |
| 3. Proof-move teaching | 4 | 4 | Now teaches BOTH forward and backward membership reasoning. |
| 4. Inventory design | 3+ | 3+ | `rcases` properly documented. `norm_num` exploit on L09 is new but minor. |
| 5. Hint design and recoverability | 3 | 3 | L10 hints guide through both new skills well. No `Branch` still. |
| 6. Worked example -> practice -> transfer -> boss | 3 | 3 | Boss still does not exercise newest skills. |
| 7. Mathematical authenticity | 4 | 4 | Nodup failure case strengthens authenticity. |
| 8. Paper-proof transfer | 3 | 3+ | L10's proof has a natural English translation. |
| 9. Technical fit and maintainability | 3+ | 3+ | No change. |

**Average: 3.3.** All categories >= 3. No automatic red flags triggered.

---

## 9. Ranked Patch List

### P0 (Blocking)

None.

### P1 (High)

None.

### P2 (Medium -- non-blocking)

1. **Add `norm_num` to L09's `DisabledTactic`.** The intended proof never uses `norm_num`, and it closes the entire statement. This is a secondary exploit vector that can be closed without affecting the deliberate `simp` trade-off.
   - Current: `DisabledTactic decide native_decide simp_all aesop`
   - Proposed: `DisabledTactic decide native_decide norm_num simp_all aesop`

2. **(Carried from R3)** Add `DisabledTheorem` for shortcut lemmas on L03-L06, L10, L11.

3. **(Carried from R3)** Document focused subgoal syntax (`cdot`).

4. **(Carried from R3)** Add `Branch` alternatives for `use` in L05, `Or.inl` in L03.

5. **(Carried from R3, modified)** Consider strengthening L07. Still a single-rewrite level.

6. **(New, low priority)** Consider adding a sentence to L10's conclusion explicitly calling back to L04 as the forward counterpart: "In Level 4, you used `List.mem_append` to prove membership in a concatenation. Here you used it in the opposite direction."

### P3 (Low -- polish)

7. L09's `simp` exploit remains by design. No change recommended.

---

## 10. What to Playtest Again After Patching

If P2-1 (`norm_num` disabled on L09) is implemented:
- Verify L09's intended proof still works (it should -- `norm_num` is never used in the intended proof).
- No full re-audit needed.

If P2-2 through P2-5 (carried from R3) are implemented:
- Targeted verification of affected levels. Same recommendations as R3.

No changes require a full re-audit.

---

## 11. Overall Verdict

**PASS.** The R4 enrichment changes are well-implemented and improve the world in two specific ways:

1. **L09's conjunction** successfully demonstrates both Nodup success and the membership fact that blocks a different Nodup, satisfying the plan and the R3 coverage gap. The `simp` exploitability profile is unchanged (the new conjunct is also closable by `simp`). A minor new finding: `norm_num` also closes the statement (P2, easily fixable by adding it to `DisabledTactic`).

2. **L10's backward reasoning** is the most important improvement across all four audit rounds. Teaching `rw [...] at h` and `rcases` here seeds the dominant proof pattern for downstream finset worlds (W6-W8). The two skills are introduced together because they are complementary (get a disjunction, then split it), and the level's hints and documentation are thorough.

3. **The boss's non-use of `rcases`** is a noted coverage gap (P2) but not blocking. The boss integrates the world's primary skill family (forward membership reasoning). The `rcases` skill is seeded and will be exercised extensively in downstream worlds.

The world delivers on its promise. It teaches genuine proof moves, has proper tactic gating, and now covers both forward and backward membership reasoning. Rubric average 3.3, no category below 3, no P0 or P1 issues.

**Remaining items are P2 polish**, the most actionable being adding `norm_num` to L09's disabled tactics.
