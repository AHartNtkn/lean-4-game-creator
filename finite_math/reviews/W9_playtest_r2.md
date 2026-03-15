# W9 FinsetCardinality -- Playtest Audit (Round 2)

## R1 correction verification

| R1 claim | Coordinator correction | R2 verdict | Evidence |
|----------|----------------------|------------|----------|
| "`omega` undeclared -- add `NewTactic omega`" | FALSE: declared in W1 L01 | **CONFIRMED FALSE.** `omega` appears in `NewTactic omega exact intro «have» assumption apply rw constructor use cases` at `Game/Levels/FinIntro/L01_WhatIsFin.lean` line 121. Once declared anywhere in the game, it is globally available. No action needed. | File verified. |
| "Boss doesn't test inclusion-exclusion" | FALSE: Boss Part 2 uses `card_union_add_card_inter` | **CONFIRMED FALSE.** L09 Boss Part 2 is `exact Finset.card_union_add_card_inter _ _` (line 49). The boss directly tests inclusion-exclusion. | File verified. |

Both corrections confirmed. These are closed.

---

## 1. Overall verdict

**CONDITIONAL PASS.** The world has no P0 (blocking) defects after verifying that the R1 claims were false. There is one P1 issue (`simp` missing from DisabledTactic -- already flagged by enrichment R1 and R2) and several P2 issues. The world structure is clean, the narrative is coherent, and the boss tests all three main lemma families introduced (range, inclusion-exclusion, filter-bound). However, the world is pedagogically shallow: every level is a one-step proof, and the `simp` omission makes most levels trivially bypassable.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Covers 6 new lemmas + 2 retrievals. The "insertion peeling" strategy is described but never exercised -- gap in proof-move closure. |
| 2. Granularity fit | 3 | Each level isolates one lemma. No level is too broad. Some are arguably too fine (L01, L02 are trivially short), but this is acceptable for first-contact + retrieval. |
| 3. Proof-move teaching | 2 | Every level is a single `exact` or `rw`. No multi-step reasoning anywhere. The peeling strategy is described in L03's conclusion but never practiced. The world teaches "which lemma to use" but not "how to combine lemmas." |
| 4. Inventory design | 3 | 6 new theorems introduced at appropriate times. `refine` used in boss is known from W3/W3_ex. DisabledTactic is missing `simp` (P1). |
| 5. Hint design | 3 | Two-layer hints (strategy + hidden code) on every level. Consistent pattern. No misfiring risk because proofs are single-step. |
| 6. Progression | 2 | The boss is three independent single-lemma applications joined by a conjunction -- it tests retrieval, not integration. No level requires combining lemmas. Support is never faded because it is never needed. |
| 7. Mathematical authenticity | 3 | Good transfer moments (additive vs subtractive inclusion-exclusion). Good misconception handling (C9: 0-indexing). Concrete examples throughout. |
| 8. Paper-proof transfer | 3 | Transfer paragraphs in L03, L07, L09. Consistent "In plain language" sections in conclusions. |
| 9. Technical fit | 3 | Compiles. Dependencies are sane. World fits the W9 slot in the plan. |
| **Average** | **2.78** | Below the 3.0 threshold due to proof-move teaching and progression weaknesses. |

---

## 3. Coverage gaps

| Gap | Severity | Detail |
|-----|----------|--------|
| Insertion peeling strategy never exercised | P2 | L03 conclusion describes a 3-step strategy (peel inserts, singleton, arithmetic) but no level requires executing it. This is a proof-move layer gap. |
| `card_empty` never used in combination | P2 | L01 introduces `card_empty` but it never appears as a step in a larger proof. |
| No level requires producing a non-membership proof | P2 | L03 hands the learner `h : a ∉ s`. In real use, the learner must derive `a ∉ s` themselves. |
| Disjoint-union case not taught | P2 | `card_union_of_disjoint` (the simple case of inclusion-exclusion) is not introduced. The general case is taught without the special case. |

---

## 4. Granularity defects

| Defect | Severity | Detail |
|--------|----------|--------|
| Boss is a gauntlet, not an integrator | P2 | L09 concatenates three independent single-lemma applications. No part requires combining moves from different levels. Each part is exactly as hard as the level that introduced the lemma. See failure taxonomy item 8b (gauntlet boss). |
| No multi-step level anywhere in the world | P2 | Every proof is 1-2 steps. The world's center of gravity is "lemma recognition" rather than "cardinality reasoning." |

---

## 5. Learner simulation

### Attentive novice

**First likely stuck point**: L06, where the learner must produce a conjunction. The `constructor` tactic for `∧` goals was taught in W1 (NNG4 baseline), but this is the first time the learner sees it in the context of finset cardinality. The hint ("Split the conjunction with `constructor`") rescues well.

**Most likely wrong move**: In L03, the novice might try `rw [Finset.card_insert_of_notMem]` without supplying the hypothesis `h`. The hidden hint covers this by showing both `rw [Finset.card_insert_of_notMem h]` and `exact Finset.card_insert_of_notMem h`. This is a good rescue.

**Hint rescue quality**: Good across all levels. The two-layer pattern (strategy hint visible, code hint hidden) is consistent and appropriate for single-step proofs.

**Lesson legibility**: Each level's lesson is clearly stated in the introduction and reinforced in the conclusion. The learner knows what they are practicing. However, the lessons are uniformly shallow: "apply this one lemma." The learner never experiences the satisfaction of combining multiple lemmas into a non-trivial proof.

**Overall novice experience**: The novice will progress smoothly but will not develop cardinality proof skills. They will learn to recognize 6 lemma names and apply each one in isolation. They will not know how to compute `({1, 2, 3} : Finset Nat).card = 3` from scratch, despite being told the method in L03's conclusion.

### Experienced Lean user

**Avoidable friction**: None. The experienced user will enjoy the clean single-step proofs. The world is too easy for them, but that is by design (lecture world, not pset).

**Alias gaps**: None detected. `exact` and `rw` both work for each level. The hidden hints show both options.

**Inventory clutter**: Minimal. 6 new theorems are well-organized in the Finset doc group.

**`simp` exploit**: The experienced user will notice that `simp` closes L01, L02, L05, and both parts of L06 instantly. This is the primary friction point for this user: the world feels like busywork because `simp` (or `norm_num`) handles everything.

**`rfl` exploit**: Some goals (L01, L02, L05) may be closable by `rfl` since the cardinalities of concrete finsets are definitionally computable. This cannot be disabled and is a known P2 issue (accept as `rfl` is never disableable).

**`norm_num` exploit**: `norm_num` is not disabled and likely closes L01, L02, L05, and both parts of L06 (and possibly L07, L08 since all finsets are concrete). This is a P2 issue.

**`omega` exploit**: `omega` does not understand `Finset.card` and cannot close these goals directly. Not an exploit vector here.

---

## 6. Boss integrity (L09)

| Check | Status | Detail |
|-------|--------|--------|
| Seeded subskills | PASS | All three lemmas (card_range, card_union_add_card_inter, card_filter_le) are taught in L05, L07, L08 respectively. |
| Closure quality | WEAK | Each boss part is identical in difficulty to the corresponding introduction level. No escalation. |
| Integration quality | FAIL (P2) | No part requires combining lemmas from different levels. The boss is three independent retrieval exercises bundled in a conjunction. This matches failure taxonomy item 8b (gauntlet boss). |
| Surprise burden | PASS | No untaught skills. `refine` for conjunction splitting is known from W3/W3_ex. |
| Can the learner explain why the proof works? | PASS | Each part is self-explanatory: "I applied the matching lemma." But this is a low bar. |

**Boss verdict**: The boss tests retrieval, not integration. It is functional but does not meet the standard for a boss that "reveals weakness." A learner who memorized the lemma names but cannot combine them would pass this boss. This is a P2 issue, not P0/P1, because the boss does technically use inclusion-exclusion as claimed.

---

## 7. Technical risks

| Risk | Severity | Detail |
|------|----------|--------|
| `simp` not disabled | P1 | `simp` is absent from all 9 DisabledTactic lines. The standard set (per project memory) is `trivial decide native_decide simp aesop simp_all`. `simp` closes L01, L02, L05, L06 (both parts), and possibly L07/L08 with appropriate simp lemmas. This allows bypassing the intended lesson on ~5 of 9 levels. |
| `norm_num` not disabled | P2 | `norm_num` is absent from all 9 levels. It likely closes L01, L02, L05, L06 since these are concrete Nat equalities/conjunctions. Other worlds (W3_ex, W4, W6) disable `norm_num` where it bypasses lessons. |
| `rfl` closes concrete cardinality equalities | P2 (accept) | L01 `(∅).card = 0`, L02 `({42}).card = 1`, L05 `(range 5).card = 5` are likely definitionally true. `rfl` cannot be disabled. Known systemic issue. |
| L01 intro claims `card_singleton` and `card_insert_of_notMem` were used "in passing" previously | P2 | The intro says "You have already seen `Finset.card` in passing -- you used `card_singleton` and `card_insert_of_notMem` to compute the size of literal finsets." This should be verified: did W8_ex actually use these lemmas? If the learner never used them before, the intro is misleading. Enrichment R1 flagged this (suggestion 9). |
| No `TheoremDoc` for `Finset.mem_range` | P2 | L05 introduces `Finset.mem_range` in the text ("To reason about membership: `Finset.mem_range : m ∈ Finset.range n ↔ m < n`") but does not add it as `NewTheorem` or provide a `TheoremDoc`. The learner reads about it but cannot find it in their theorem panel. If the world intends to introduce it, it should be declared. If not, it should be removed from the introduction text or clearly marked as "for reference only." |

---

## 8. Ranked patch list

| Rank | Issue | Severity | Fix | Levels affected |
|------|-------|----------|-----|-----------------|
| 1 | `simp` missing from DisabledTactic | P1 | Add `simp` to every DisabledTactic line: `DisabledTactic trivial decide native_decide simp aesop simp_all` | L01-L09 |
| 2 | `norm_num` not disabled | P2 | Add `norm_num` to DisabledTactic on levels where it bypasses the lesson (at minimum L01, L02, L05, L06) | L01, L02, L05, L06 |
| 3 | Boss is a gauntlet (three independent single-lemma apps) | P2 | Redesign at least one boss part to require multi-step reasoning. E.g., Part 1 could ask `({1, 2, 3} : Finset Nat).card = 3` requiring the peeling strategy. Or combine inclusion-exclusion with numerical verification. | L09 |
| 4 | No multi-step cardinality computation level | P2 | Add a level between L04 and L05 requiring the peeling strategy (chain `card_insert_of_notMem` + `card_singleton`). | New level |
| 5 | `Finset.mem_range` mentioned in L05 text but not in inventory | P2 | Either add `NewTheorem Finset.mem_range` with `TheoremDoc`, or remove from introduction text | L05 |
| 6 | L01 intro makes unverified claim about prior use of `card_singleton`/`card_insert_of_notMem` | P2 | Verify whether W5-W8_ex used these lemmas. If not, revise intro text to "You will now meet..." instead of "You have already seen..." | L01 |

---

## 9. What to playtest again after patching

- **If only the DisabledTactic fix (rank 1) is applied**: Re-audit is likely unnecessary. Verify `simp` appears in all 9 lines and that no other automation tactic was accidentally omitted. A quick scan suffices.
- **If `norm_num` is also added (rank 2)**: Same -- mechanical verification, no full re-audit needed.
- **If the boss is redesigned (rank 3) or a new multi-step level is added (rank 4)**: Full re-audit (R3) is needed. The new content must be checked for exploitability, hint quality, granularity, and integration. These are structural changes that affect the world's proof-move teaching and progression scores.
- **If only text/inventory fixes are applied (ranks 5-6)**: No re-audit needed.

**Minimum for clean pass**: Apply rank 1 (add `simp` to DisabledTactic). This eliminates the only P1 issue. The P2 issues are real but not blocking -- they represent opportunities for improvement, not defects that would confuse or mislead the learner.
