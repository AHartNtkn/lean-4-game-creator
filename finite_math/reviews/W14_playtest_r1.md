# W14 RangeSumInduction -- Playtest Audit R1

**World**: RangeSumInduction (9 levels, LECTURE)
**Dependency**: FinsetSum -> RangeSumInduction
**Auditor**: playtest-auditor R1
**Build status**: Compiles (8268 jobs, 0 errors)

---

## 1. Overall Verdict

**Needs revision.** The world teaches the induction-on-range-sums pattern well and the boss is solid, but there are two blocking issues: (1) `norm_num` is not disabled and closes L01/L02 in one shot, bypassing the intended lesson; (2) L05 and L07 have identical statements, which is overfine. Several medium-priority issues also need attention.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | All boss subskills seeded. No coverage gaps within the world. |
| Granularity fit | 2 | L05=L07 identical statement; L03=L04 identical statement (defended by different dominant lesson but L07 is not). |
| Proof-move teaching | 3 | Clear three-step template (induction / base case / peel+ih+ring). Well articulated. |
| Inventory design | 3 | `sum_range_succ` and `calc` properly introduced. Disabled tactic set is correct modulo `norm_num` gap. |
| Hint design & recoverability | 3 | Hints are layered (strategy visible, code hidden). Calc hints show full plan at top level. |
| Worked example -> practice -> boss | 3 | Good progression L02 (demo) -> L03 (first proof) -> L05/L06 (practice) -> L09 (boss). |
| Mathematical authenticity | 3 | Sum of odds identity (L06) is beautiful. Geometric interpretation in conclusion. Transfer moment in boss conclusion. |
| Paper-proof transfer | 4 | Boss conclusion contains explicit paper-proof translation. Excellent. |
| Technical fit | 3 | Compiles cleanly. Build info messages are benign (upstream TacticDocs exist). |

**Average: 3.0** (passes threshold but two categories at 2 require fixes)

---

## 3. Coverage Gaps

No major coverage gaps within the world's scope. All boss subskills are introduced and practiced before L09.

Minor notes:
- `Finset.range_zero` and `Finset.sum_empty` are used in L08 but introduced upstream (FinsetCardinality L06, FinsetSum L02). No `NewTheorem` needed here since they're already in inventory.
- `omega` is mentioned in text (L05, L08) as an alternative to `ring` but never actually required. This is fine -- it's a known tool from FinIntro L01.

---

## 4. Granularity Defects

### P1 -- L05 and L07 have identical statements

Both prove `∑ i in range n, 2 = 2 * n`. L05 teaches the `rw [sum_range_succ, ih]; ring` pattern. L07 re-does it with `calc`. But `calc` was already taught in L04. The learner has already seen both the formula (L05) and calc (L04). L07 is a clone, not a transfer problem.

**Fix**: Either (a) give L07 a different formula (e.g., `∑ i in range n, 3 = 3 * n` or `∑ i in range n, (i + 1) = n * (n + 1) / 2` -- though Nat division is tricky -- or `∑ i in range n, (2 * i) = n * (n - 1)` if that works), or (b) merge L07 into the boss coaching by removing it and letting L06's conclusion serve as the "you're ready" checkpoint, or (c) replace L07 with a genuinely new formula that specifically coaches the calc pattern on harder algebra (e.g., a three-step calc on L06's identity).

### P2 -- L03 and L04 have identical statements

Both prove `∑ i in range n, 1 = n`. L03 teaches induction+sum_range_succ for the first time; L04 teaches `calc` on the same proof. The duplicate statement is justified here because L04's dominant lesson (calc syntax) is genuinely new and using familiar math reduces novelty burden. Borderline acceptable, but ideally L04 would use a slightly different formula to avoid deja vu.

### P2 -- L08 ordering feels late

The base case pitfalls (range 0 = empty) lesson appears at L08, after the learner has already done the base case with `rfl` five times (L03-L07). By L08, the base case is automatic. Teaching the mechanism (`range_zero` + `sum_empty`) late means the learner must retroactively understand something they've been doing unconsciously.

**Fix**: Consider moving L08 to L03 (before the first induction proof) so the learner understands WHY `rfl` works before relying on it. Then the current L03 becomes L04, etc. Alternatively, make L08 a case where `rfl` does NOT suffice (e.g., prove `∑ i in range 0, (i + 1) = 0` where the RHS is 0 but the function isn't constant 0, so the learner must use `range_zero` and `sum_empty` explicitly). Wait -- `rfl` does close `∑ i in range 0, (i + 1) = 0` because the sum over empty range is definitionally 0. So the current L08 approach (universally quantified over f) is actually the right way to force explicit rewriting. The ordering concern remains.

---

## 5. Statement Exploitability

### P1 -- L01: `norm_num` closes in one shot

`(Finset.range 5).card = 5` is closed by `norm_num` (or `norm_num [Finset.card_range]`). `norm_num` is available (introduced in FinCompute L05, not disabled here). The intended lesson (use `Finset.card_range`) is bypassed.

**Fix**: Add `norm_num` to `DisabledTactic` on L01.

### P1 -- L02: `norm_num` closes in one shot

`∑ i in Finset.range 4, i = (∑ i in Finset.range 3, i) + 3` is a concrete numeric equality. `norm_num` evaluates it directly. The intended lesson (apply `sum_range_succ`) is bypassed.

**Fix**: Add `norm_num` to `DisabledTactic` on L02.

### P2 -- L03/L04/L05/L07: `Finset.sum_const` bypass

These levels can all be solved without induction by using `rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]` (for L03/L04) or adding `ring` (for L05/L07). This bypasses the intended induction lesson. However, `Finset.sum_const` is never taught in this course, so only experienced mathlib users would find it. P2 severity.

**Fix (optional)**: Could use `DisabledTheorem Finset.sum_const` on L03-L07, but this may be over-aggressive. The bypass requires chaining 4 untaught lemmas; a learner who can do that arguably knows what they're doing.

### P2 -- L06: No single-tactic bypass found

`∑ i in range n, (2 * i + 1) = n ^ 2` requires induction. `norm_num`, `omega`, and `ring` cannot close it without the induction + sum_range_succ structure. Good.

### OK -- L09 Boss: No bypass found

The boss requires induction. `ring` alone does not work. The intended proof path is the only reasonable one. Good.

---

## 6. Interactive Proof Quality

### P2 -- L04, L07: `calc` blocks require multi-line input

The `calc` block must be typed as a single multi-line construct. In lean4game, this is mitigated by the fact that each `:= by` subgoal within calc CAN be filled in interactively once the calc structure is typed. However, the learner must first type the calc skeleton (the intermediate expressions) correctly before any feedback appears on the individual steps.

The hints show the full calc block, which helps. But the operational lesson about calc hints misfiring is relevant: hints inside calc steps fire AFTER the learner already chose the intermediate expression. The hard part (choosing intermediate expressions) gets no per-step feedback.

**Mitigation already present**: Both L04 and L07 show the complete calc block in the strategy hint. The learner can copy-paste or type along. This is acceptable for a first-contact level (L04) where the goal is to learn the syntax, but L07 repeating this pattern adds no value (see granularity defect above).

---

## 7. Learner Simulation

### Attentive Novice

**First likely stuck point**: L03, the inductive step. After `induction n with`, the novice sees `| zero =>` and `| succ n ih =>` syntax for the first time in this context. They may not remember the exact syntax from NNG4 (if it was long ago). The hint rescues well by showing the structure.

**Most likely wrong move**: In L05, after `rw [sum_range_succ, ih]`, the novice may try `rfl` (which worked before) instead of `ring`. The hint fires at the right point and directs them to `ring`. Good rescue.

**Hint legibility**: Generally good. Strategy hints explain what to do; hidden hints give exact code. The layering is correct throughout.

**L04 calc**: The novice will need to type a multi-line construct they've never seen before. The hint shows the exact code, but typing multi-line expressions in the game interface is unfamiliar. First stuck point for calc. The level introduction does a good job explaining the syntax, but practice will be needed.

**L08 confusion**: By L08, the novice has used `rfl` for the base case 5 times. Being told to use `rw [range_zero, sum_empty]` instead may be confusing ("why can't I just use rfl?"). The introduction explains this but the motivation ("what if rfl doesn't work?") is hypothetical. The level doesn't actually present a case where `rfl` fails.

### Experienced Lean User

**Avoidable friction**: L01 and L02 are trivial for an experienced user. `norm_num` closes both instantly, and since it's available, they'll use it. The intended `rw [card_range]` lesson is a non-event for them.

**L03/L04 redundancy**: An experienced user will find L04 tedious -- they already proved the same thing in L03, and `calc` on this trivial example feels forced.

**L05=L07 redundancy**: An experienced user will immediately notice they're proving the same thing again. This is friction without payoff.

**Alias gaps**: None found. `rw [Finset.sum_range_succ]` is the standard form. The fully qualified name is used consistently.

**`norm_num` availability**: An experienced user will use `norm_num` on L01 and L02. Since it's not disabled, this works. They bypass the lesson but at least it doesn't break anything.

---

## 8. Boss Integrity (L09)

### Seeded subskills
- `induction n with`: Introduced L03, practiced L04-L07. SEEDED.
- `rfl` for base case: Introduced L03, used in L04-L07. SEEDED.
- `Finset.sum_range_succ`: Introduced L02, used in L03-L07. SEEDED.
- `rw [ih]`: Introduced L03, used in L04-L07. SEEDED.
- `ring`: Used in L05-L07. SEEDED (introduced upstream in FinsetExploration).

### Closure quality
All subskills have full closure: introduction, supported practice, retrieval, and integration. The boss integrates all five moves. GOOD.

### Integration quality
The boss formula `4*i + 3 = n*(2n+1)` is new surface form. The ring step `n*(2n+1) + (4n+3) = (n+1)*(2(n+1)+1)` is genuinely harder than any practiced example. The learner must plan: induction, then sum_range_succ, then ih, then ring. GOOD.

### Surprise burden
None. Every move in the boss has been practiced. The only "new" element is the specific formula, which is appropriate surface novelty. GOOD.

### Can the learner explain why the proof works?
Yes. The boss conclusion contains an explicit paper-proof translation that maps each Lean step to its mathematical counterpart. EXCELLENT.

### Verdict: Boss is well-designed. No defects.

---

## 9. Course-Role Sanity

**Intended role**: LECTURE world on induction with range sums.

**Actual role**: The world teaches the induction-on-range-sums proof template through progressive examples. This is a lecture world. The progression from worked example (L02-L03) through practice (L04-L07) to boss (L09) follows the lecture pattern correctly.

**L08 (base case pitfalls)**: Acts as a "warning" level -- explaining why something works under the hood. This is a valid lecture role, but its placement late in the world (after 5 uses of the thing it explains) weakens its impact.

**Transfer**: The boss conclusion contains an excellent transfer moment mapping Lean steps to paper-proof language. This is the world's primary transfer point. GOOD.

---

## 10. Technical Risks

1. **Build warnings**: "No world introducing `induction`, but required by RangeSumInduction" -- `induction` is an NNG4 prerequisite. This warning is benign (the tactic is available, just never formally `NewTactic`-declared in this course). Low risk but could be cleaned up by adding `induction` to an appropriate `NewTactic` line upstream (e.g., FinsetInduction L01 which is about induction).

2. **Hint in L01 mentions `norm_num`**: The visible hint says "Use `norm_num [Finset.card_range]` to compute the cardinality." This actively directs learners to `norm_num`, undermining the lesson (`rw [card_range]`). If `norm_num` is disabled (per P1 fix), this hint must be updated.

---

## 11. Ranked Patch List

| # | Sev | Level(s) | Issue | Fix |
|---|-----|----------|-------|-----|
| 1 | P1 | L01 | `norm_num` closes goal, bypassing `card_range` lesson | Add `norm_num` to `DisabledTactic`. Update hint to remove `norm_num` suggestion. |
| 2 | P1 | L02 | `norm_num` closes goal, bypassing `sum_range_succ` lesson | Add `norm_num` to `DisabledTactic`. |
| 3 | P1 | L07 | Identical statement to L05 (overfine) | Replace with a different formula or merge/remove. See suggestions below. |
| 4 | P2 | L04 | Identical statement to L03 (borderline overfine) | Consider using a slightly different formula for calc demo. Low priority if L07 is fixed. |
| 5 | P2 | L08 | Late ordering -- base case mechanism taught after 5 uses | Consider moving to L03 position (before first induction proof). Or make it a case where `rfl` genuinely fails. |
| 6 | P2 | L03-L07 | `Finset.sum_const` bypass for experienced users | Consider `DisabledTheorem Finset.sum_const` on L03-L07. Optional. |
| 7 | P2 | L01 | Hint text actively suggests `norm_num` | If norm_num is disabled, rewrite hint to only suggest `rw [Finset.card_range]`. |

### Suggested fix for L07 (patch #3):

Replace L07's statement with a formula the learner hasn't seen, specifically designed for calc walkthrough. Options:
- `∑ i in range n, (3 * i + 2) = n * (3 * n + 1) / 2` -- but Nat division is problematic.
- `∑ i in range n, (2 * i) = n * (n - 1)` -- Nat subtraction is also tricky.
- Best option: `∑ i in range n, (i + 1) = n * (n + 1) / 2` -- same Nat division issue.
- Simplest clean option: `∑ i in range n, 3 = 3 * n` -- but this is just L05 with 3 instead of 2 (overfine again).
- Recommended: Use a formula with polynomial RHS that avoids division, e.g., `∑ i in range n, (2 * i + 1) = n ^ 2` (but this IS L06). Or simply promote the calc version of L06's proof as L07 and drop the redundant re-proof of L05's formula.

---

## 12. What to Playtest Again After Patching

1. **L01, L02**: After adding `norm_num` to DisabledTactic, verify the intended proof path still works and hints are correct.
2. **L07**: After replacing the statement, verify the calc proof compiles, hints are correct, and the new formula provides genuine practice.
3. **Full world rebuild**: `lake build` after all patches.
4. **Boss re-check**: Verify the boss still integrates moves from the patched levels.

---

## Summary

The world is structurally sound with good progression, excellent transfer, and a well-designed boss. The main issues are: (1) `norm_num` must be added to DisabledTactic on L01 and L02, (2) L07 must get a different statement to avoid being a clone of L05, and (3) the L01 hint must stop recommending `norm_num`. After these fixes, the world should pass R2 cleanly.
