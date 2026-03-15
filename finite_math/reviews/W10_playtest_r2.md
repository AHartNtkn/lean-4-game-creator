# W10 FinsetInduction -- Playtest Audit R2

**World**: FinsetInduction (9 levels: L01-L09)
**Round**: 2 (verifying R1 fixes)
**Auditor**: lean4game-playtest-auditor

---

## 1. Overall verdict

**CONDITIONAL PASS -- two P2 defects remain, no P0/P1.**

The R1 fixes land correctly: `Finset.insert_union` is now seeded in L05 (removing the boss lottery), and `Nat.succ_eq_add_one` was confirmed to be a reviewer error (not used). The world compiles cleanly (warnings only, no errors). DisabledTactic coverage is mostly solid but has two `simp`-availability gaps.

---

## 2. R1 fix verification

| R1 issue | Status | Notes |
|----------|--------|-------|
| Boss lottery: `insert_union` not seeded | **FIXED** | L05 introduces `Finset.insert_union` via `NewTheorem` + `TheoremDoc`. Boss intro references it. |
| `Nat.succ_eq_add_one` needed | **Reviewer error** | Not referenced anywhere in the world. Confirmed not needed. |

---

## 3. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | `card_le_card` (L06) introduced but never retrieved or integrated (see 5.1) |
| Granularity fit | 3 | L06 is thin (single `exact`) but acceptable as first-contact. Orphaned file is clutter. |
| Proof-move teaching | 4 | Finset induction pattern taught clearly across base/step/contradiction variants |
| Inventory design | 3 | Clean. Minor: `card_union_le` missing TheoremDoc for DisabledTheorem. |
| Hint design & recoverability | 3 | Hints are well-layered. L04 `absurd` is only path shown (see 5.2). |
| Progression (worked -> practice -> boss) | 3 | Good escalation L01-L05, L07 provides contrast, L09 integrates well. L06 is an island. |
| Mathematical authenticity | 4 | Solid connection between induction on Nat and Finset. Transfer moments in conclusions. |
| Paper-proof transfer | 4 | Every conclusion has a plain-language paragraph. L09 transfer section is excellent. |
| Technical fit | 3 | Compiles. Orphaned file. Missing TheoremDoc warning. |

**Average: 3.3** -- above the 3.0 threshold. No category below 2.

---

## 4. Technical sanity

### 4a. Build status
All 9 active levels compile. Warnings only (missing TacticDoc/TheoremDoc -- not blocking).

### 4b. Missing documentation
- **`Finset.card_union_le`**: Used as `DisabledTheorem` in L09 but has no `TheoremDoc`. Build warning emitted. **P3** (cosmetic).

### 4c. Orphaned file
- `L05_CardinalityByInduction.lean` exists in the directory but is NOT imported by `FinsetInduction.lean`. Contains `NewTheorem Finset.insert_ne_empty` and `TheoremDoc Finset.insert_ne_empty` that are unreachable. Should be deleted. **P3** (cleanup).

### 4d. DisabledTactic audit

| Level | DisabledTactic | `simp` blocked? | `omega` blocked? | `norm_num` blocked? | Issues |
|-------|---------------|-----------------|------------------|---------------------|--------|
| L01 | trivial decide native_decide aesop simp_all omega | NO | YES | NO | **P2**: `simp` and `norm_num` both close `0 + n = n` |
| L02 | trivial decide native_decide aesop simp_all | NO | - | - | OK: `simp` alone cannot close this goal |
| L03 | trivial decide native_decide aesop simp_all | NO | - | - | OK: `simp` alone cannot close this goal |
| L04 | trivial decide native_decide aesop simp_all | NO | - | - | Marginal: `simp [h]` closes goal but requires passing hypothesis |
| L05 | trivial decide native_decide aesop simp_all | NO | - | - | OK: `simp` alone cannot close this goal |
| L06 | trivial decide native_decide aesop simp_all | NO | - | NO | **P2**: `simp` and `norm_num` both close the concrete inequality |
| L07 | trivial decide native_decide aesop simp_all simp | YES | - | NO | `simp` disabled correctly. But `norm_num` closes goal. |
| L08 | trivial decide native_decide aesop simp_all | NO | - | - | OK: `simp` alone cannot close this goal |
| L09 | trivial decide native_decide aesop simp_all | NO | - | - | OK: `simp` alone cannot close this goal |

### 4e. DisabledTheorem audit

| Level | DisabledTheorem | Adequate? |
|-------|----------------|-----------|
| L02 | `Finset.eq_empty_or_nonempty` | YES -- blocks the one-shot |
| L03 | `Finset.card_eq_zero` | YES -- blocks the library iff |
| L04 | `Finset.Nonempty.card_pos Finset.card_pos` | YES -- blocks dot-notation and function form |
| L05 | `Finset.card_insert_le` | YES -- forces the learner to prove it |
| L07 | `Finset.card_range` | YES -- blocks the library version |
| L08 | `Finset.eq_empty_or_nonempty Finset.card_pos` | YES -- blocks both one-shot paths |
| L09 | `Finset.card_union_le` | YES -- blocks the library version |

### 4f. Statement exploitability

| Level | Exploitable? | Details |
|-------|-------------|---------|
| L01 | P2 | `simp` / `norm_num` close the goal. `omega` correctly disabled. Induction lesson bypassed. |
| L02 | Clean | No one-shot available after disabling `eq_empty_or_nonempty` |
| L03 | Clean | No one-shot after disabling `card_eq_zero`. `simp` cannot close. |
| L04 | Marginal | `simp [h]` closes goal, but requires learner to know `simp` can handle `Nonempty`. Not a typical novice move. |
| L05 | Clean | No one-shot after disabling `card_insert_le` |
| L06 | P2 | `simp` / `norm_num` close the concrete statement without engaging `card_le_card` |
| L07 | Marginal | `norm_num` closes the goal (simp correctly disabled). `norm_num` is not commonly known to close Finset goals. |
| L08 | Clean | No one-shot available |
| L09 | Clean | No one-shot available |

---

## 5. Coverage sanity

### 5.1. `card_le_card` is orphan coverage

`Finset.card_le_card` is introduced in L06 (first-contact) but never used again in the world -- not in the boss, not in any practice level, not in any integration. The conclusion of L06 says "This is used frequently in combinatorics" but the world never demonstrates that.

Coverage state: **I only** (introduce, no S/R/G/T).

This is failure taxonomy #4 (Surface coverage only). **P2** severity because the theorem IS useful and the learner has seen it, but the lack of retrieval or integration means it won't stick.

### 5.2. `absurd` as hidden prerequisite

L04 teaches the vacuous base case pattern using `exact absurd h Finset.not_nonempty_empty`. The term combinator `absurd` has never been formally introduced (`NewTactic`, `TacticDoc`, or a dedicated first-contact level). It appeared in a hint in FinIntro L07 but was never the dominant lesson.

The alternative path (`exfalso` + `exact Finset.not_nonempty_empty h`) works and uses only taught moves, so this is not blocking. But the primary hint directs the learner to `absurd` without teaching it. **P2** severity -- hints should prefer taught vocabulary.

### 5.3. Coverage items tracked

| Item | Axis | First contact | Supported | Retrieved | Integrated | Transfer |
|------|------|--------------|-----------|-----------|------------|----------|
| Finset induction principle | MOVE | L02 | L03, L04 | L07 (choice) | L09 | L09 conclusion |
| `card_insert_of_notMem` with `ha` | MOVE | L03 | L04 | L05, L07 | L09 | - |
| Vacuous base case (`absurd`) | MOVE | L04 | - | - | - | L04 conclusion |
| `by_cases` on membership | MOVE | L05 | - | - | - | L05 conclusion |
| `card_le_card` | MATH | L06 | - | - | - | L06 conclusion |
| Nat vs Finset induction choice | MOVE | L07 | - | - | - | L07 conclusion |
| `refine` for induction | LEAN | L08 | - | - | - | - |
| `insert_union` decomposition | MOVE | L05 (doc) | - | - | L09 | - |
| `card_insert_le` | MATH | L05 (proves) | - | - | L09 | - |
| `empty_union` | MATH | L09 (boss) | - | - | L09 | - |

**Finset induction** has good closure (I -> S -> R -> G -> T).
**`card_le_card`** has weak closure (I only).
**`by_cases` on membership** has weak closure in this world (I only), but was practiced in FinsetOperations.
**`refine` for induction** has weak closure (I only), but `refine` itself was practiced in earlier worlds.

---

## 6. Granularity sanity

### 6a. Level assessment

| Level | Role | Dominant lesson | Granularity | Notes |
|-------|------|----------------|-------------|-------|
| L01 | Review | Nat induction recall | OK | Familiar ground, sets up comparison |
| L02 | First-contact | Finset.induction_on syntax | OK | Simple goal, ih not needed -- isolates syntax |
| L03 | Supported practice | Using ih + card_insert_of_notMem | OK | First real induction proof |
| L04 | Supported practice | Vacuous base case pattern | OK | Teaches the other base case shape |
| L05 | First-contact | by_cases + card_insert_le proof + insert_union intro | Slightly broad | Two theorems introduced (card_insert_le proved, insert_union doc'd) |
| L06 | First-contact | card_le_card | Thin | Single `exact` proof. Acceptable for first-contact but borderline. |
| L07 | Transfer | Nat vs Finset induction choice | OK | Good conceptual contrast |
| L08 | Practice | refine alternative syntax | OK | Shows alternative style |
| L09 | Boss | Integration of all moves | OK | 4+ distinct moves required |

### 6b. Boss integrity (L09)

- **Seeded subskills**: `induction using Finset.induction_on` (L02-L04), `insert_union` (L05), `card_insert_le` (L05), `card_insert_of_notMem` (prior world + L03-L04), `empty_union` (new in boss but trivial), `omega` (prior worlds), `have` (prior worlds). All seeded except `empty_union`, which is simple enough to be introduced in a boss.
- **Closure quality**: Good -- no lottery items after R1 fix.
- **Integration quality**: The proof requires combining 4 distinct lemmas + the inductive hypothesis. Not a gauntlet -- the `have` + `omega` pattern requires genuine planning.
- **Surprise burden**: Low. The intro provides a proof skeleton.
- **Can learner explain why the proof works?**: Yes -- the conclusion explicitly addresses this.

### 6c. World center of gravity
Coherent: "proving properties of finsets by building from empty via insertion." All levels serve this theme. L06 (`card_le_card`) is the weakest connection -- it's related but not directly about the induction principle.

---

## 7. Learner simulation

### 7a. Attentive novice

**First likely stuck point**: L04 base case. The learner sees `h : (∅ : Finset α).Nonempty` and the goal `0 < (∅ : Finset α).card`. The hint says to use `absurd`, which may be unfamiliar. The learner might try `omega` (which fails -- `omega` doesn't know `∅.card = 0` without help). Alternative: `exfalso` then `exact Finset.not_nonempty_empty h` works with taught moves but is not in the hints.

**Most likely wrong move**: In L03, trying `omega` immediately without rewriting `card (insert a s')` first. The hint system catches this because the first hint fires on the insert case and tells the learner to rewrite.

**Hint rescue quality**: Good overall. Hints are layered (strategy visible, code hidden). L07's hidden hint shows a multi-line proof block which is appropriate for that level of difficulty.

**Lesson legibility**: Clear in all levels. Each introduction explains what's new, each conclusion summarizes.

### 7b. Experienced Lean user

**Avoidable friction**:
- L01 is a Nat induction warm-up that experienced users will find trivial. Acceptable as a review level.
- L06 is a single `exact`. An experienced user completes it in 2 seconds. Acceptable as first-contact.

**Alias gaps**:
- `Finset.card_eq_zero` is disabled in L03 but not in L06-L09. Not an issue since it's not needed after L03.
- No missing aliases detected.

**Inventory clutter**: Low. New theorems are introduced judiciously (1-2 per level max).

**Needless forced verbosity**:
- L09 boss requires explicit `have` statements with full type annotations. This is appropriate for the integration level.
- L07 requires a `have hmem` block with a sub-proof. Appropriate for teaching the pattern.

---

## 8. Course-role sanity

| Level | Intended role | Actual role | Match? |
|-------|-------------|-------------|--------|
| L01 | Review | Review of Nat induction | YES |
| L02 | First-contact | First Finset.induction_on proof | YES |
| L03 | Supported practice | Using ih + contradiction | YES |
| L04 | Supported practice | Vacuous base case | YES |
| L05 | First-contact + seeding | by_cases proof + boss prep | YES |
| L06 | First-contact | card_le_card introduction | YES but island (no follow-up) |
| L07 | Transfer | Choosing between induction types | YES |
| L08 | Practice | Alternative syntax | YES |
| L09 | Boss | Full integration | YES |

---

## 9. Ranked patch list

### P2 (Medium -- should fix before shipping)

**P2-1: L01 exploitable via `simp` / `norm_num`**
`simp` closes `0 + n = n` instantly. `norm_num` also closes it. Neither is disabled.
**Fix**: Add `simp norm_num` to L01's `DisabledTactic` line.
**Why it matters**: L01's lesson is Nat induction recall. If `simp` closes it, the learner skips induction entirely.

**P2-2: L06 exploitable via `simp` / `norm_num`**
The concrete statement `({1, 2} : Finset Nat).card <= ({1, 2, 3} : Finset Nat).card` is closed by `simp` or `norm_num` because the finsets are concrete and decidable.
**Fix**: Add `simp norm_num` to L06's `DisabledTactic` line.
**Why it matters**: L06's lesson is `card_le_card`. If `simp` closes it, the learner never sees the theorem.

### P2 (Medium -- quality improvement)

**P2-3: L07 exploitable via `norm_num`**
`norm_num` closes `(Finset.range n).card = n`. `simp` is already disabled but `norm_num` is not.
**Fix**: Add `norm_num` to L07's `DisabledTactic` line.

**P2-4: `card_le_card` has surface-only coverage**
Introduced in L06, never retrieved. Not used in the boss.
**Fix**: No code change needed in this round. Flag for the enrichment reviewer to consider adding a level that uses `card_le_card` in combination with other moves, or integrating it into the boss.

**P2-5: L04 hints prefer `absurd` over taught vocabulary**
The hints direct the learner to `exact absurd h Finset.not_nonempty_empty`, but `absurd` was never formally taught. An alternative path using `exfalso` + `exact` exists.
**Fix**: Add a Branch or modify the visible hint to suggest `exfalso` first, with the `absurd` version as a hidden alternative. Or add `absurd` as a `NewTactic` with `TacticDoc` somewhere before L04.

### P3 (Low -- cosmetic / cleanup)

**P3-1: Missing TheoremDoc for `Finset.card_union_le`**
L09 has `DisabledTheorem Finset.card_union_le` without a `TheoremDoc`. Causes a build warning.
**Fix**: Add `TheoremDoc Finset.card_union_le as "Finset.card_union_le" in "Finset"` before the `DisabledTheorem` line in L09.

**P3-2: Orphaned file `L05_CardinalityByInduction.lean`**
Not imported, not used. Contains dead `TheoremDoc` and `NewTheorem` entries. Should be deleted to avoid confusion.
**Fix**: Delete the file.

---

## 10. What to playtest again after patching

If P2-1, P2-2, and P2-3 are fixed (adding `simp norm_num` to DisabledTactic for L01, L06, L07):
- Re-verify those three levels compile and cannot be closed by automation.
- No full re-audit needed -- the fixes are mechanical DisabledTactic additions.

If P2-4 or P2-5 are addressed (structural changes to hints or adding a level):
- Re-audit the affected levels only.

**Verdict**: The world is shippable after fixing P2-1, P2-2, P2-3. The remaining P2 items (P2-4, P2-5) are quality improvements that can be addressed in a future pass.
