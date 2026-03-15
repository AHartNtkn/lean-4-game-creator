# Playtest Audit (Round 2): W3 ListBasics

**Auditor**: playtest-auditor (adversarial)
**World**: W3 -- Lists: construction and operations
**World type**: Lecture
**Levels audited**: L01 through L11 (11 levels)
**Build status**: Compiles (verified, `lake build` succeeds with 0 errors)
**Prior audit**: `reviews/W3_ListBasics_playtest.md` (round 1 -- FAILING)

---

## 0. Prior P0 Issue Resolution Check

The round-1 audit identified these P0 (blocking) defects:

| R1 # | R1 P0 Issue | Status in R2 | Detail |
|-------|------------|--------------|--------|
| 1 | All statements fully concrete / decidable; zero structural proofs | **FIXED** | 9 of 11 levels now use symbolic/universally-quantified statements requiring structural proof. Only L01 (rfl warmup) and L08 (Fin-indexing, rfl) are concrete. |
| 2 | `decide` and `simp` not gated | **FIXED** | `DisabledTactic decide native_decide` on all 11 levels. `simp` additionally disabled on 6 levels (L03, L04, L05, L06, L10, L11). See exploitability section for residual issues. |
| 3 | `List.Nodup` (M17) missing entirely | **FIXED** | L09 is a dedicated `List.Nodup` level with `nodup_cons` unfolding, `nodup_nil` base case, and explicit discussion of the bridge to W4. |
| 4 | Fake boss (decide in one step) | **FIXED** | L11 boss requires 7 tactic steps integrating `mem_filter`, `mem_map`, `constructor`, `refine`, and `rfl`. Cannot be closed by `decide` or `simp` (both disabled). |

**All four R1 P0 issues are resolved.** The world has been completely re-authored.

---

## 1. Overall Verdict

**CONDITIONAL PASS.** The world is a genuine teaching instrument. The transformation from round 1 is dramatic: every core level now requires structural proofs with real tactic decisions, the boss integrates multiple skills, `Nodup` is taught, and the learner has real learning moments. There are residual P1 and P2 issues that should be fixed (primarily exploitability via `aesop` and via one-liner library lemmas, plus `simp` availability in two levels that should require manual reasoning), but the world is shippable after addressing these.

---

## 2. Rubric Scores

| Category | R1 Score | R2 Score | Notes |
|----------|----------|----------|-------|
| 1. Coverage closure | 1 | 3 | M16 (I, S, G), M17 (I), N11 (I, S), N12 (I, S). `Nodup` bridge present. Length, membership, map, filter, append all covered with structural proofs. Missing: no `List.Perm` preview, no counterexample for `Nodup`-failure (discussed textually but not proved). |
| 2. Granularity fit | 1 | 3 | Each level isolates one dominant lesson. Good variation in proof shapes. L07 and L08 are slightly thin (one-rewrite and rfl respectively). L09 is the longest at ~8 steps, appropriate for the concept. |
| 3. Proof-move teaching | 0 | 4 | Excellent. Teaches: `rw` with API lemmas, `left`/`right` for disjunctions, `constructor` for conjunctions, `refine` for partial proofs, `exact` with hypotheses, navigating nested `Or`. Each proof move is isolated at introduction and combined later. |
| 4. Inventory design | 2 | 3 | Well-sequenced introduction of definitions and theorems. `refine` introduced at L05, `simp` at L09, `left`/`right` at L03. All documented with `DefinitionDoc`/`TheoremDoc`/`TacticDoc`. Minor: `List.get` introduced without a theorem doc (only definition doc). |
| 5. Hint design and recoverability | 1 | 3 | Strategy-then-tactic hints at each step. L10 and L11 have 5-6 hints guiding through multi-step proofs. Hints describe what the goal looks like and what to try. No pure spoilers. Minor: L07 has only 1 hint (but the level is simple). Hints do not cover common wrong moves (see learner sim). |
| 6. Worked example -> practice -> transfer -> boss | 0 | 3 | Clear progression: L01 (warmup), L02-L06 (first-contact per API function), L07-L08 (review/connection), L09 (new concept), L10 (retrieval/combination), L11 (boss integration). Transfer moments in conclusions. Scaffolding present and appropriately faded. |
| 7. Mathematical authenticity | 2 | 4 | Introductions explain WHY each operation matters, not just HOW to use it. Conclusions include paper-proof translations. The `Nodup` level explicitly discusses the List-Multiset-Finset hierarchy. The `Fin`-indexing level connects back to W1. Counterexample for `Nodup` discussed in text (good). |
| 8. Paper-proof transfer | 2 | 3 | Every conclusion has an "In plain language" translation. L11 boss conclusion maps tactic steps to English sentences. L10 conclusion explains the "nested disjunction navigation" pattern. The proofs themselves have step-by-step structure that transfers. Minor: no level where the learner must *produce* a paper-proof statement (but this is appropriate for a lecture world). |
| 9. Technical fit and maintainability | 2 | 3 | Compiles. Dependencies sane. World coherent. Level naming follows conventions. `import Mathlib` is heavyweight but consistent with the project convention. |

**Average: 3.2** (up from 1.2). All categories >= 3. No red flags triggered from the rubric's automatic list.

---

## 3. Coverage Analysis

### 3a. Plan Alignment

| Plan # | Plan level | R2 Implementation | Match |
|--------|-----------|-------------------|-------|
| 1 | cons and empty list | L01 (ListCons) | YES |
| 2 | List membership | L03 (ListMem) -- reordered to #3 | Acceptable reorder |
| 3 | `List.length` | L02 (ListLength) -- reordered to #2 | Acceptable reorder |
| 4 | `List.append` | L04 (MemAppend) -- reframed as membership in append | Improved: symbolic instead of concrete |
| 5 | `List.map` | L05 (ListMap) -- membership preservation | Improved: structural proof |
| 6 | `List.filter` | L06 (ListFilter) -- membership preservation | Improved: structural proof |
| 7 | `List.Nodup` | L09 (Nodup) | YES -- moved to later position, which is fine |
| 8 | Boss | L11 (Boss) | YES -- integrates map, filter, membership |

**Added levels not in plan**: L07 (AppendLength), L08 (FinIndexing), L10 (Practice). These are all beneficial additions:
- L07 practices `rw` with a second list lemma (reinforcement)
- L08 connects lists to `Fin` from W1 (cross-world connection)
- L10 is a retrieval exercise combining L03 + L04 skills (scaffolding for boss)

**Plan alignment verdict**: Good. The plan's coverage is fully implemented, with beneficial additions. Level reordering is justified (length before membership makes the rw-pattern available for the membership level).

### 3b. Coverage Item Status

| Item | Axis | Plan State | R2 State | Gap? |
|------|------|-----------|----------|------|
| M16 (List basic API) | MATH | I, S, G | I (L01), S (L02-L07), G (L11) | None |
| M17 (List.Nodup) | MATH | I | I (L09) | None |
| N11 (`::` notation) | NOTATION | I | I (L01), used in L02-L03 | None |
| N12 (`++` notation) | NOTATION | I | I (L04), practiced in L07, L10 | None |
| V1 (unfolding a definition) | MOVE | Review from W1 | Practiced via `rw` with API lemmas throughout | None |
| V18 (`have` for subgoals) | MOVE | Review from W1 | Not explicitly required in any level | P2 -- acceptable, `constructor` fills the role |

### 3c. Proof-Move Coverage (Dramatically Improved)

| Move | R1 Status | R2 Status |
|------|-----------|-----------|
| `rw` with API lemma | Never used | Core pattern in L02, L03, L04, L05, L06, L07, L09, L10, L11 |
| `left` / `right` | Never used | Introduced L03, practiced L04, L10 |
| `constructor` | Never used | Introduced L06, practiced L09, L11 |
| `refine` with `?_` | Never used | Introduced L05, practiced L11 |
| `exact` with hypothesis | Never used | Used in L04, L06, L10, L11 |
| Nested disjunction navigation | Never used | L10 (retrieval) |
| `rfl` for definitional equality | Overused | Appropriate in L01, L08 |

### 3d. Missing Coverage (Minor)

| Item | Axis | Status | Severity |
|------|------|--------|----------|
| `List.Perm` preview | MATH | Not mentioned until L11 conclusion | P2. The plan says M17 is "setup for multisets." The conclusion of L11 mentions permutations as a preview, which is good. No action needed. |
| Counterexample for `Nodup`-failure | EXAMPLE | Discussed textually in L09 conclusion but not proved | P2. Having the learner *prove* that `[1,2,1]` does NOT satisfy `Nodup` would strengthen the concept. Currently only verbal. |
| `have` tactic | MOVE | Not required in any level | P2. Acceptable since `constructor` serves a similar structural-decomposition role. |

---

## 4. Granularity Analysis

### 4a. Level-by-level dominant lesson check

| Level | Dominant Lesson | Proof Steps | Verdict |
|-------|----------------|-------------|---------|
| L01 | `List` constructors and `[a,b,c]` notation | 1 (`rfl`) | Fine: warmup, definitional equality |
| L02 | `rw` with `List.length_cons` (symbolic) | 1 (`rw`) | Fine: first-contact for `rw`-with-list-lemma pattern |
| L03 | Membership via `List.mem_cons`, `left`/`right` | 3 (`rw`, `left`, `rfl`) | Good: clean first-contact |
| L04 | Membership in append via `List.mem_append` | 3 (`rw`, `left`, `exact`) | Good: transfers L03 pattern to new API |
| L05 | Map preserves membership, `refine` tactic | 3 (`rw`, `refine`, `rfl`) | Good: new proof move (existential witness) |
| L06 | Filter membership, `constructor` for `∧` | 4 (`rw`, `constructor`, `exact`, `exact`) | Good: new proof move (conjunction) |
| L07 | `rw` with `List.length_append` | 1 (`rw`) | Slightly thin but serves as retrieval for L02's pattern |
| L08 | `List.get` and Fin-indexing connection | 1 (`rfl`) | Slightly thin but conceptually important cross-world link |
| L09 | `List.Nodup`, recursive unfolding pattern | ~8 steps | Good: appropriate length for the concept. Teaches iterative `rw [nodup_cons]` + `constructor` |
| L10 | Retrieval: combining `mem_cons` + `mem_append` | 5 steps | Good: no new material, tests retrieval of earlier skills |
| L11 | Boss: integrating filter, map, constructor, refine | 7 steps | Good: genuine integration, planning challenge |

### 4b. Center of gravity

The world's center of gravity is **list API lemma-based reasoning via `rw`**. Every level from L02 onward teaches or practices rewriting with a specific list API lemma and then handling the resulting logical structure (disjunctions, conjunctions, existentials). This is coherent and stable.

### 4c. Difficulty progression

```
L01 [*------] warmup (1 step, rfl)
L02 [**-----] first rw (1 step, but symbolic)
L03 [***----] first multi-step (3 steps, new tactic: left)
L04 [***----] same pattern, new lemma (3 steps)
L05 [****---] new pattern: existential (3 steps, new tactic: refine)
L06 [****---] new pattern: conjunction (4 steps, uses constructor)
L07 [**-----] retrieval (1 step, easy rw)
L08 [**-----] concept bridge (1 step, rfl)
L09 [******-] longest proof, recursive unfolding (8 steps)
L10 [*****--] retrieval, combining 2 lemmas (5 steps)
L11 [*******] boss, all skills (7 steps)
```

The progression is broadly good. L07-L08 are an intentional dip before the climb to L09-L11, which is acceptable (it provides a breather before the hardest material). The boss is appropriately the most complex level.

### 4d. Granularity defects

| Defect | Severity | Detail |
|--------|----------|--------|
| L07 is a single-rewrite level | P2 | It's essentially `rw [List.length_append]` and done. This is very similar to L02's structure (single `rw`). Justifiable as retrieval/reinforcement but thin. Could be enhanced with a follow-up step (e.g., `omega` for arithmetic after the rewrite). |
| L08 is a single-rfl level | P2 | `rfl` on a concrete `List.get` evaluation. Conceptually important (Fin-indexing) but pedagogically identical to L01 (warmup rfl). The introduction carries the teaching weight; the proof is trivial. |
| L07 and L09 have `simp` available but are intended for manual reasoning | P1 | See exploitability section. Both can be solved by `simp` alone, bypassing the intended lesson. |

---

## 5. Statement Exploitability (Section 1b)

### 5a. Automation exploits

| Level | `decide` | `simp` | `aesop` | `omega` | Assessment |
|-------|----------|--------|---------|---------|------------|
| L01 | Disabled | N/A (rfl is fine) | Works | N/A | Fine. `rfl` is the intended proof; `aesop` closing it is harmless. |
| L02 | Disabled | **Not disabled; closes it** | Works | No | **P1**. `simp` is not disabled and closes the goal, bypassing `rw [List.length_cons]`. The learner can skip the lesson. |
| L03 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes it. |
| L04 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes it. |
| L05 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes it. |
| L06 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes it. |
| L07 | Disabled | **Not disabled; closes it** | Works | No | **P1**. Same as L02 -- `simp` bypasses the intended `rw`. |
| L08 | Disabled | N/A (rfl is fine) | Works | N/A | Fine. |
| L09 | Disabled | **Not disabled; closes it** | Works | N/A | **P1**. `simp [List.nodup_cons]` (or even bare `simp`) closes the entire 8-step proof. This is the most severe case: the longest, most conceptually important level in the world is trivially closable by a tactic the learner already has. |
| L10 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes it. |
| L11 | Disabled | Disabled | Works | N/A | **P1**. `aesop` closes the boss. |

### 5b. Library-lemma one-liner exploits

| Level | One-liner | Bypasses lesson? |
|-------|-----------|-----------------|
| L03 | `exact List.mem_cons_self` | Yes -- skips learning `rw [List.mem_cons]` + `left` + `rfl` pattern |
| L04 | `exact List.mem_append_left _ h` | Yes -- skips learning `rw [List.mem_append]` + `left` + `exact` |
| L05 | `exact List.mem_map_of_mem h` | Yes -- skips `rw [List.mem_map]` + `refine` + `rfl` |
| L06 | `exact List.mem_filter.mpr ⟨hmem, hpred⟩` | Yes -- skips `rw [List.mem_filter]` + `constructor` + `exact` |
| L10 | `exact List.mem_cons_of_mem _ (List.mem_append_right _ h)` | Yes -- skips all 5 steps |
| L11 | `exact List.mem_filter.mpr ⟨List.mem_map_of_mem h, hp⟩` | Yes -- boss one-liner |

### 5c. Exploitability verdict

**The `aesop` problem is systemic and severe.** Every level from L03 through L11 (9 of 11 levels, including the boss) can be closed by `aesop` in a single step. `aesop` is not disabled anywhere in the world. A learner who discovers `aesop` can skip the entire world. This is a P0 defect by the audit criteria ("can the learner pass WITHOUT doing what the dominant lesson teaches? If yes, the statement must be redesigned or the trivial proof path must be disabled").

**However**: `aesop` is a relatively obscure tactic that a post-NNG4 learner is unlikely to know. The more realistic exploit is `simp` on L02, L07, and L09, where `simp` is available and closes the goal. A learner who tries `simp` on L02 (because they were taught `simp` in their NNG4 follow-up or tried it experimentally) will succeed and may develop the habit of trying `simp` first on every level, which would bypass L07 and the critical L09.

**Recommendation**: Disable `aesop` on all levels (or at minimum L03-L11). Disable `simp` on L02 and L07 (it is already appropriately available in L09 where `simp` is part of the intended proof, but see below). For L09, consider whether the intended proof should use `simp` for the non-membership subgoals or whether a different approach would be more educational.

**On the library-lemma one-liners**: These are harder to prevent without `DisabledTheorem`. The specific lemmas (`List.mem_cons_self`, `List.mem_append_left`, `List.mem_map_of_mem`, `List.mem_filter.mpr`) are the "shortcut" forms of the unfolded reasoning the levels teach. For a lecture world, the intended approach is to teach the unfolding; the one-liners are expert paths that a post-NNG4 learner is unlikely to find. This is P2 severity -- ideally these would be disabled via `DisabledTheorem` for the relevant levels, but it is not blocking.

### Revised exploitability severity

| Issue | Severity |
|-------|----------|
| `aesop` closes L03-L11 | **P0** |
| `simp` closes L02, L07 (not disabled) | **P1** |
| `simp` closes L09 (the Nodup level -- the longest, most important level) | **P1** |
| Library one-liners bypass L03-L06, L10, L11 | P2 |

---

## 6. Interactive Proof Quality (Section 1c)

### 6a. Step-by-step interactivity

Every multi-step level (L02-L07, L09-L11) provides visible goal-state changes after each tactic. The learner can type one step, inspect the result, and decide what to do next. This is a complete reversal from R1.

| Level | Steps | Each step changes goal visibly? | Verdict |
|-------|-------|---------------------------------|---------|
| L01 | 1 | Yes (closes) | Fine |
| L02 | 1 | Yes (closes) | Fine |
| L03 | 3 | Yes: `rw` transforms goal, `left` focuses, `rfl` closes | Good |
| L04 | 3 | Yes: same pattern | Good |
| L05 | 3 | Yes: `rw` transforms, `refine` provides witness and leaves `?_`, `rfl` closes | Good |
| L06 | 4 | Yes: `rw` transforms, `constructor` splits, `exact` closes each | Good |
| L07 | 1 | Yes (closes) | Fine |
| L08 | 1 | Yes (closes) | Fine |
| L09 | ~8 | Yes: each `rw [nodup_cons]` transforms, each `constructor` splits, each `simp` closes a concrete subgoal, `exact List.nodup_nil` closes base case | Good |
| L10 | 5 | Yes: each step visibly progresses | Good |
| L11 | 7 | Yes: each step visibly progresses through filter then map layers | Good |

### 6b. Potential confusion points

- **L05**: The hint suggests both a 3-step approach (`rw` + `refine` + `rfl`) and a 1-step approach (`exact ⟨a, h, rfl⟩`). The 1-step approach gives the learner zero intermediate feedback. The introduction should more strongly emphasize the step-by-step approach. *Severity*: P2 (the step-by-step path is the guided one; the one-liner is presented as an "or" alternative).

- **L09**: After `constructor`, the learner sees two focused subgoals. The first is handled by `simp` (for the non-membership check). The transition between focused goals (using `·`) is not explained. If the learner doesn't know `·` syntax, they may be confused by the branching. *Severity*: P2 (hints guide through each branch, but the `·` syntax is not documented).

- **L11 (Boss)**: The `refine ⟨a, h, ?_⟩` step requires the learner to type angle brackets with specific arguments, which is a somewhat complex expression. However, this was taught in L05, so it should be familiar. *Severity*: P2 (retrieval, not first-contact).

---

## 7. Learner Simulation

### 7a. Attentive Novice

**Profile**: Completed NNG4. Comfortable with `rw`, `exact`, `apply`, `intro`. New to lists.

**Experience of the re-authored world**:

1. **L01**: Reads about list constructors and `::`. Goal: `[1,2,3] = 1 :: 2 :: 3 :: []`. Types `rfl`. Quick warmup. Understands notation. (Good start.)

2. **L02**: Reads about `List.length`. Goal: `(0 :: l).length = l.length + 1`. Thinks "this looks symbolic -- I need a lemma." Reads the hint about `List.length_cons`. Types `rw [List.length_cons]`. Goal closes. "Ah, so I use `rw` with list API lemmas to unfold definitions." (Key pattern learned.)

3. **L03**: Reads about membership. Goal: `5 ∈ 5 :: l`. Reads about `List.mem_cons` and tries `rw [List.mem_cons]`. Sees `5 = 5 ∨ 5 ∈ l`. Remembers `left`/`right` from... wait, this is the first time `left` appears. Reads the introduction which explains the strategy. Types `left`. Sees `5 = 5`. Types `rfl`. Learns disjunction tactics. (Good first-contact with `left`/`right`.)

4. **L04**: Similar pattern with `mem_append`. The novice recognizes the structure from L03: "unfold with `rw`, choose a disjunct, close with hypothesis." Types `rw [List.mem_append]`, `left`, `exact h`. Smooth. (Transfer from L03.)

5. **L05**: Reads about `List.map` and `List.mem_map`. Goal involves an existential. Reads about `refine`. Types `rw [List.mem_map]`. Sees `∃ a_1 ∈ l, f a_1 = f a`. This is new: an existential witness. Tries `refine ⟨a, h, ?_⟩`. Sees `f a = f a`. Types `rfl`. (Good -- new proof pattern for existentials.)

   **First likely stuck point**: The novice may not know how to provide an existential witness. `refine ⟨...⟩` syntax may be unfamiliar even after NNG4. The hint guides through it, but the angle-bracket anonymous constructor syntax is a burden. The introduction explains both the step-by-step and one-shot approach, which helps.

6. **L06**: Filter membership. The novice sees `∧` (conjunction) and needs `constructor`. This was practiced in NNG4 so it should be familiar. The level flows well after L05's pattern. (Good.)

7. **L07**: Length of append. Simple `rw` exercise. Quick. (Retrieval of L02 pattern.)

8. **L08**: `List.get` with `Fin`. Reads about the connection to W1. Goal is `rfl`. Quick. (Cross-world connection established.)

9. **L09**: `List.Nodup`. This is the longest level. The novice reads about the recursive structure of `Nodup`. Types `rw [List.nodup_cons]`. Sees `1 ∉ [2,3] ∧ [2,3].Nodup`. Types `constructor`. Handles the non-membership with `simp`. Then repeats for `[2,3]` and `[3]`. Finally reaches `[].Nodup` and uses `exact List.nodup_nil`.

   **Second likely stuck point**: After the first `constructor`, the novice must handle the branching syntax (focusing with `·`). If they type `simp` without focusing, they may see unexpected behavior. The hint guides them, but this is a genuine learning moment.

   **Most likely wrong move**: Typing `rw [List.nodup_cons]` on the wrong subgoal, or trying `rfl` where `simp` is needed.

10. **L10**: Combining `mem_cons` and `mem_append`. The novice must navigate two layers of disjunction. This is a genuine retrieval exercise -- no new material, but the combination is harder than any individual level. The hint chain guides through each step. (Good practice.)

11. **L11 (Boss)**: Integrating filter, map, and membership. The novice must plan: "first unfold filter, then handle the conjunction (map membership + predicate), then unfold map, then provide the witness." With hints at each step, the novice should succeed. Without hints, this would be a genuine challenge.

    **Can the novice explain why the proof works?** Yes: "To show f(a) is in the filtered mapped list, I need to show it's in the mapped list AND it satisfies the predicate. It's in the mapped list because a is in the original list. The predicate is given."

**Overall novice experience**: The novice learns genuine proof patterns and builds toward real integration. The world is no longer a glossary. **Estimated time**: 30-45 minutes. **Skill acquired**: Using `rw` with API lemmas, navigating `∨` with `left`/`right`, splitting `∧` with `constructor`, providing existential witnesses with `refine`.

### 7b. Experienced Lean User

**Profile**: Comfortable with Lean 4. Has used lists before. Taking this course for finite math content.

**Experience**:

1. L01: `rfl`. Quick.
2. L02: Sees the goal. Knows `simp` would work (and it does -- `simp` is not disabled). Types `simp`. Done. **Does not learn the `rw [List.length_cons]` pattern.**
3. L03: `decide` and `simp` are disabled. May try `exact List.mem_cons_self` (works). Or `aesop` (works). Does not engage with the `rw`/`left`/`rfl` pattern.
4. L04-L06: Similar -- `aesop` or library one-liners close everything.
5. L07: `simp` works.
6. L08: `rfl`.
7. L09: `simp` works.
8. L10-L11: `aesop` works.

**The experienced user clears the world in under 3 minutes using `aesop` and `simp`.** They learn nothing about the intended proof patterns.

**Assessment**: The experienced user would benefit from `aesop` being disabled. The library one-liners are harder to prevent and are arguably acceptable expert paths. But `aesop` as a universal bypass is not acceptable.

**Avoidable friction**: None (the expert has zero friction, which means zero engagement -- the same problem as R1 for this audience segment, though now caused by `aesop` rather than `decide`).

---

## 8. Boss Integrity (L11)

### Boss: "Map, filter, and membership"

**Statement**: Given `a ∈ l` and `p (f a) = true`, prove `f a ∈ List.filter p (List.map f l)`.

**Required subskills**:
1. `rw [List.mem_filter]` -- from L06
2. `constructor` -- from L06
3. `rw [List.mem_map]` -- from L05
4. `refine ⟨a, h, ?_⟩` -- from L05
5. `rfl` -- baseline
6. `exact hp` -- baseline
7. Planning: decompose filter-of-map into filter layer + map layer

**Seeded subskills check**:
- [x] `rw [List.mem_filter]` -- taught in L06, first contact
- [x] `constructor` for `∧` -- taught in L06, first contact; reinforced in L09
- [x] `rw [List.mem_map]` -- taught in L05, first contact
- [x] `refine ⟨..., ?_⟩` -- taught in L05, first contact
- [x] `rfl` -- NNG4 baseline
- [x] `exact` with hypothesis -- used throughout

**Closure quality**: Every boss skill has been introduced and practiced. The boss requires 4 distinct taught skills in combination. No untaught micro-skills. PASS.

**Integration quality**: The boss is NOT a gauntlet (taxonomy #8b). The learner must plan which layer to peel first (filter, then map). The composition filter-of-map creates a genuine interaction: the map membership feeds into the filter conjunction, requiring the learner to see the structure. The planning challenge is: "what order do I unfold in?" PASS.

**Surprise burden**: The boss is longer (7 steps) than any individual earlier level except L09 (8 steps). But L09 is repetitive (same 2-step pattern three times + base case), while the boss has 7 distinct steps. This is an appropriate scale-up. No surprise. PASS.

**Can the learner explain why the proof works?**: "I need f(a) to be in the filtered mapped list. By the filter characterization, that means f(a) is in the mapped list AND p(f(a)) is true. The predicate part is given. For the map part, I need to show there's something in l that maps to f(a) -- that something is a itself." YES. PASS.

**Boss verdict**: Genuine integration boss. PASS (contingent on fixing `aesop` exploit).

---

## 9. Course-Role Sanity

The world is a **Lecture** world. Required behaviors:

| Requirement | R1 Status | R2 Status |
|-------------|-----------|-----------|
| Introduces new concepts (via text AND proof) | Text only | PASS: text + structural proofs |
| First-contact with new proof moves | None | PASS: `rw`-with-API, `left`/`right`, `constructor`, `refine` |
| Worked examples with visible proof structure | None | PASS: L02-L06 are first-contact worked examples |
| Builds toward integrative boss | None | PASS: L11 integrates 4+ skills |
| Practice levels for mastery | None | PASS: L07, L08 (retrieval), L10 (combination) |
| Transfer moments | Text only | PASS: text transfer in conclusions |

**Role assessment**: The world now functions as a genuine lecture. PASS.

---

## 10. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| `aesop` not disabled anywhere | **P0** | Every multi-step level (L03-L11) is closable by `aesop` in one step. Must disable. |
| `simp` not disabled in L02, L07 | **P1** | These levels are intended to teach `rw` with specific lemmas. `simp` bypasses the lesson. |
| `simp` not disabled in L09 | **P1** | The most important new-concept level in the world. `simp` alone (bare, no arguments) closes the entire 8-step proof. The intended proof uses `simp` only for the non-membership subgoals, but bare `simp` at the top level skips everything. Consider restructuring to avoid this, or disable `simp` and use `norm_num` or `decide` for the concrete checks (but `decide` is already disabled). |
| No `DisabledTheorem` for library shortcut lemmas | P2 | `List.mem_cons_self`, `List.mem_append_left`, `List.mem_map_of_mem`, `List.mem_filter.mpr`, `List.mem_cons_of_mem`, `List.mem_append_right` all provide one-liner bypasses. |
| `import Mathlib` in every file | P2 | Heavyweight. Consistent with project convention. |
| Focused subgoal syntax (`·`) not documented | P2 | Used in L06, L09, L11 proofs but no `TacticDoc` for the focusing dot. Learners who don't know `·` may be confused. |
| L09 conclusion mentions `[1,2,1]` failing `Nodup` but doesn't prove it | P2 | A counterexample level would be stronger. |

---

## 11. Ranked Patch List

### P0 (Blocking)

1. **Disable `aesop` on L03-L11.** Add `aesop` to `DisabledTactic` for every level where `decide`, `simp`, or both are already disabled. This is the single remaining structural exploit that allows the entire world to be bypassed. Without this fix, the world's teaching value is contingent on the learner not knowing `aesop`.

### P1 (High -- should fix)

2. **Disable `simp` on L02 and L07.** These levels teach `rw` with a specific API lemma. `simp` closes the goal without engaging with the lemma. Add `simp` to the `DisabledTactic` line on both levels.

3. **Address `simp` exploitability on L09.** This is the hardest to fix because `simp` is part of the *intended* proof for the non-membership subgoals. Options:
   - (a) Accept that `simp` can close the whole thing, since the learner is supposed to learn `simp` in this level anyway and the introduction explains the step-by-step approach. (Current state.)
   - (b) Restructure the level to use a symbolic list (e.g., `a :: b :: c :: []` with hypotheses `a ≠ b`, `a ≠ c`, `b ≠ c`) so that `simp` cannot evaluate the non-membership concretely. This would force the learner through the `nodup_cons` unfolding. But it significantly changes the level and may be too complex for a first-contact.
   - (c) Use `List.Nodup` on a longer list so that `simp` times out or requires arguments. Unreliable.

   **Recommendation**: Option (a) with a compromise -- move the `NewTactic simp` to L07 (where `simp` is currently available and useful for `length_append`), so that by L09 the learner has already seen `simp` and the level can focus on `nodup_cons` structure with `simp` as a known supporting tool. This doesn't fix the exploit but makes the pedagogical framing cleaner.

4. **Add `aesop` to `DisabledTactic` on L01 and L08 as well for consistency**, even though these levels are `rfl`-closable anyway. This prevents the habit of typing `aesop` first.

### P2 (Medium -- nice to fix)

5. **Add `DisabledTheorem` for shortcut lemmas on relevant levels.** At minimum: disable `List.mem_cons_self` on L03, `List.mem_append_left`/`List.mem_append_right` on L04, `List.mem_map_of_mem` on L05, `List.mem_cons_of_mem` on L10. This forces the unfolding-based proof.

6. **Document the focused subgoal syntax (`·`).** Add a `TacticDoc` for `·` (or at least mention it in the introduction of L06 where it first appears in the guided proof).

7. **Add a counterexample level for `Nodup`.** Between L09 and L10 (or as part of L09), have the learner prove `¬ [1, 2, 1].Nodup` to see what goes wrong when duplicates exist. This would require inserting a level and renumbering.

8. **Strengthen L07 with a second step.** Instead of pure `rw [List.length_append]`, consider a statement like `(l₁ ++ l₂).length + 1 = l₁.length + l₂.length + 1` requiring `rw [List.length_append]` followed by `ring` or another step. This would distinguish it more clearly from L02.

9. **Add a hint in L05 for learners who try `use` instead of `refine`.** A learner familiar with NNG4's `use` tactic might try `use a` for the existential, which may or may not work depending on how the goal is structured after `rw [List.mem_map]`. A `Branch` or hint for this path would improve recoverability.

---

## 12. What to Playtest Again After Patching

After implementing the patches above:

1. **All levels after disabling `aesop`**: Verify the intended proofs still work and no other enabled tactic provides a trivial bypass.
2. **L02 and L07 after disabling `simp`**: Verify `rw` is the only short proof path.
3. **L09 if restructured**: Re-simulate the novice experience with the new structure.
4. **Boss (L11)**: Re-verify it requires genuine integration after `aesop` and shortcut lemmas are disabled.
5. **Any new levels** (counterexample, L07 enhancement): Full first-audit treatment.

---

## 13. Summary of Defects by Taxonomy

| Taxonomy # | Defect | Where | Severity | R1 Status |
|-----------|--------|-------|----------|-----------|
| #8 Fake boss | Boss closable by single tactic | L11 via `aesop` | P0 | Was P0 (via `decide`), now P0 (via `aesop`) |
| #12 Syntax dominates math | N/A | N/A | Resolved | Was present in R1 |
| #3 Overfine | N/A | N/A | Resolved | Was present in R1 |
| #4 Surface coverage only | N/A | N/A | Resolved | Was present in R1 |
| #6 Spoiler hint | N/A | N/A | Resolved | Was present in R1 |
| #13 Expert hostility | `aesop` bypass makes expert path trivial | L03-L11 | P1 | Was `decide` bypass |

---

## 14. Final Assessment

The re-authored W3 is a dramatically improved world. The round-1 audit identified a completely hollow world with zero proof moves, and the re-author has produced a world with genuine structural proofs, a coherent progression, a real boss, and solid coverage of the List API. The transformation is comprehensive and thorough.

The single remaining P0 issue is the `aesop` exploit. Every multi-step level can be bypassed by `aesop`, which is not disabled anywhere. This is the same *class* of defect as the round-1 `decide` exploit (a single tactic closes everything), but it affects a narrower audience (learners who know `aesop` are rarer than those who know `decide`). Nevertheless, it must be fixed: add `aesop` to `DisabledTactic` on all levels.

After fixing the `aesop` gate and the `simp` availability on L02/L07, this world is ready for deployment.

**Bottom line**: Dramatic improvement. One P0 fix (`aesop` gating) and two P1 fixes (`simp` gating on L02, L07) needed before the world is fully shippable. All round-1 P0 issues are resolved.
