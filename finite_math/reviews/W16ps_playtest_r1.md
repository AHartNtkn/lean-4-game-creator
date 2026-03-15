# W16_ps BigOpPset — Playtest Audit R1

**World**: BigOpPset (W16_ps)
**Role**: Pset (8 levels)
**Predecessor**: BigOpAdvanced (W16)
**Auditor**: playtest-auditor
**Date**: 2026-03-15

---

## 1. Overall Verdict

**NEEDS REVISION** — The world compiles and the DisabledTactic baseline is correct on all 8 levels. However, the boss is a **gauntlet boss** (structurally identical to L01 and L07 — same 3-step induction pattern, no novel integration demand). Additionally, three levels (L01, L02, L07) intended to force induction retrieval can be bypassed by library lemmas (`sum_const`, `prod_const`) taught in the predecessor world.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good spread across V3, V11, V20, M25, M26, M38, T2, T10. But boss does not integrate M25 as planned. |
| 2. Granularity fit | 3 | Each level isolates one retrieval target. L04 and L05 are perhaps overly thin (single-tactic). |
| 3. Proof-move teaching | 2 | L01/L07/L08 all teach the exact same proof shape. Boss does not add a novel planning challenge. |
| 4. Inventory design | 3 | No new items (correct for pset). DisabledTactic baseline present. |
| 5. Hint design / recoverability | 3 | All hints hidden (correct for pset). Adequate rescue. |
| 6. Worked example -> practice -> transfer -> boss | 2 | Transfer levels (L06/L07) are well designed. But boss fails the integration test — it is a clone of L01/L07. |
| 7. Mathematical authenticity | 3 | Sum of odd numbers = n^2 is a great identity. Geometric interpretation in conclusion is excellent. |
| 8. Paper-proof transfer | 4 | L06 and L07 are strong transfer exercises. L08 conclusion includes paper correspondence. |
| 9. Technical fit / maintainability | 3 | Compiles. Dependencies correct. Translation warnings expected (i18n). |

**Average**: 2.89 — Below the 3.0 threshold. Two categories at 2 (proof-move teaching, progression).

---

## 3. Coverage Gaps

| Planned item | Status | Issue |
|-------------|--------|-------|
| V3 (induction, T) | Present in L01, L07, L08 | Bypassable via `sum_const` (see exploits) |
| V11 (sum_range_succ, T) | Present in L01, L07, L08 | Same bypass |
| V20 (algebraic manipulation, T) | Present in L03 | OK |
| M25 (multiplicative induction, T) | Present in L02 | Bypassable via `prod_const` |
| M26 (sum_comm, T) | Present in L05 | OK |
| M38 (sum_filter, T) | Present in L04 | OK |
| T10 (read sigma notation, S) | Present in L06 | OK |
| T2 (write inductive proof, R) | Present in L07 | OK |
| **Boss integration of M25** | **MISSING** | Plan says boss integrates V3+V20+M25. Actual boss uses only V3+V11+V20 (no multiplicative element). |

---

## 4. Granularity Defects

### P1: Boss is a gauntlet boss (failure taxonomy #8b)

L08 (boss) proves `sum (2*i + 1) = n^2` by induction. The proof is:
```
induction n with
| zero => rfl
| succ n ih => rw [sum_range_succ, ih]; ring
```

This is **structurally identical** to:
- L01: `sum 2 = 2*n` → `induction; rfl; rw [sum_range_succ, ih]; ring`
- L07: `sum 5 = 5*n` → `induction; rfl; rw [sum_range_succ, ih]; ring`

The boss differs only in the summand expression (`2*i + 1` vs. `2` vs. `5`). The `ring` step is trivially different. There is no novel interaction between moves, no planning challenge, no moment where the learner sees the whole structure differently. The learner who solved L01 can solve L08 by copy-pasting their L01 proof and changing the statement.

A pset boss should require 5+ integrated moves (ref: operational lessons). This boss uses 3 moves, all exercised identically in L01.

### P2: L04 and L05 are single-tactic levels

L04 is `rw [Finset.sum_filter]`. L05 is `exact Finset.sum_comm`. These are valid retrieval exercises, but each is a single tactic — the learner types one command and the level is done. For a pset, this is acceptable but borderline. Consider whether these could be combined with a follow-up step (e.g., L04 could also ask the learner to simplify the resulting conditional expression).

---

## 5. Statement Exploitability

### P2: L01, L07 bypassed by `sum_const` (no induction needed)

`∑ i ∈ range n, c = c * n` can be proved without induction:
```
rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
```

`sum_const` was taught in BigOpAdvanced L09 (the predecessor world's boss). The learner already has this tool. Using it is a valid alternative proof strategy, but it completely bypasses the intended V3/V11 retrieval.

**Severity**: P2 — The bypass uses a taught lemma (not automation), so the learner demonstrates some skill. But the plan explicitly targets induction retrieval, which is defeated.

**Possible fix**: Add `DisabledTheorem Finset.sum_const` on L01 and L07 to force induction. (This is pedagogically justified — these are retrieval levels for induction, not for `sum_const`.)

### P2: L02 bypassed by `prod_const` (no induction needed)

`∏ i ∈ range n, 3 = 3^n` can be proved:
```
rw [Finset.prod_const, Finset.card_range]
```

`prod_const` was not explicitly taught but is a library lemma directly analogous to `sum_const`. A learner who knows `sum_const` might discover `prod_const`.

**Possible fix**: Add `DisabledTheorem Finset.prod_const` on L02.

### OK: L08 boss is not exploitable by single-tactic

`omega`, `norm_num`, `ring` all fail on the boss. No single library lemma closes it (would require Gauss formula + arithmetic). The boss requires induction, which is the intended approach.

---

## 6. Interactive Proof Quality

All levels pass the interactive proof quality check:
- No elaborate one-liners
- Each step produces visible goal-state changes
- Multi-rewrite chains are at most 2 items (`rw [sum_range_succ, ih]`), which is acceptable
- L08 boss proof is 4 discrete steps (induction, rfl, rw+rw, ring)

---

## 7. Learner Simulation

### Attentive novice

**First stuck point**: L03 (algebraic manipulation). The novice must recall both `sum_add_distrib` and `← mul_sum` without hints. If they try `sum_add_distrib` first (likely), they'll see partial progress, which is good. The harder recall is `← mul_sum` — reverse rewriting a factoring lemma requires recognizing the pattern `∑ (c * f) = c * ∑ f`.

**Most likely wrong move**: On L01, trying `ring` or `omega` first (neither closes sum goals). The hidden hint will eventually rescue if clicked.

**Hint rescue**: Adequate. All hints are hidden (pset-appropriate), but each gives a clear full strategy when revealed. The novice who clicks the hint gets enough to proceed.

**Lesson legibility**: Clear on L01-L05. L06 is unusual (rfl proof, lesson in conclusion) — the novice might feel confused about why the level exists until reading the conclusion. L07 similarly — the Lean proof is identical to L01, and the value is in the conclusion text. Both transfer levels are legible once completed.

### Experienced Lean user

**Avoidable friction**: None significant. The `DisabledTactic` set is clean.

**Alias gaps**: `Finset.sum_range_succ` could also be written as `Finset.sum_range_succ'` (different variant). No issue since the learner already knows the specific name.

**Inventory clutter**: No new items introduced (correct for pset).

**`sum_const` bypass**: An experienced user will immediately use `sum_const` on L01/L02/L07 and skip induction entirely. This is the most likely expert shortcut.

---

## 8. Boss / Pset Integrity

### Boss integrity (L08)

| Check | Verdict |
|-------|---------|
| Seeded subskills | Partially — V3, V11, V20 seeded in L01-L03, L07. M25 NOT used despite plan. |
| Closure quality | Weak — same proof shape as L01/L07, no novel combination |
| Integration quality | **FAIL** — no genuine integration; the proof concatenates the same 3 moves with a new summand |
| Surprise burden | None — no new moves, identical pattern |
| Explainable proof | Yes — sum of odd numbers = n^2, strong geometric interpretation |

**Verdict**: The boss is a **gauntlet boss** (failure taxonomy #8b). It concatenates moves from L01 without requiring novel integration. Redesign needed.

### Pset integrity

| Check | Verdict |
|-------|---------|
| Fresh surface form | Yes — new constants (2, 3, 5), new predicates (< 5), new functions (f*g) |
| Reduced scaffolding | Yes — all hints hidden, no visible hints |
| Real retrieval | Partially — L01/L02/L07 can be solved without retrieving the target skill (induction) |
| Beyond lecture clones | Mostly — L03 uses a fresh expression, L04 uses a new predicate, L05 uses function arguments. L01/L07 are close to clones (same pattern, different constant). |

**Concern**: L01 and L07 are essentially clones of each other (sum of constants by induction, differing only in the constant 2 vs 5). One should be repurposed to test a different pattern.

---

## 9. Technical Risks

1. **`no level id` info messages**: All 8 levels show `no level id` info. This is cosmetic (the GameServer assigns IDs). No action needed.

2. **Translation warnings**: All 8 levels show "No translation found" warnings. Expected — i18n strings are auto-generated on build. No action needed.

3. **Missing TacticDoc info**: All 8 levels show "Missing Tactic Documentation. Using existing docstring." for the disabled tactics. These docs exist in prior worlds (MultisetHierarchy, FinThreeExamples). The info messages just mean the docs are inherited, not defined locally. No action needed.

4. **`No world introducing induction, but required by BigOpPset`**: Build warning. `induction` is a baseline NNG4 tactic, never formally introduced via `NewTactic`. This is a systemic issue across many worlds. No action needed for this world specifically.

---

## 10. Ranked Patch List

### P1 (must fix)

1. **Redesign boss (L08) to require genuine integration** — The current boss (`sum (2*i+1) = n^2`) uses the same 3-step induction pattern as L01/L07. The plan specifies the boss should integrate V3 + V20 + M25. Options:
   - (a) A multi-step proof requiring induction AND algebraic manipulation AND a multiplicative step (e.g., a combined identity involving both sums and products).
   - (b) An identity requiring `sum_add_distrib` or `← mul_sum` as intermediate steps within an induction, so the learner must plan the decomposition before applying the induction hypothesis.
   - (c) Example: `∑ i ∈ range n, (2*i+1)^2 = n*(2*n-1)*(2*n+1)/3` — requires induction + heavier `ring` work, but may be too arithmetic-heavy. Better: an identity that requires splitting sums (V20) within an inductive step.

### P2 (should fix)

2. **Add `DisabledTheorem Finset.sum_const` on L01 and L07** to force induction retrieval. The `sum_const` bypass defeats the pset's purpose for these levels.

3. **Add `DisabledTheorem Finset.prod_const` on L02** to force multiplicative induction retrieval.

4. **Differentiate L01 and L07** — Both are "sum of constants by induction" with different constants. L07's value is in the transfer conclusion, but the proof exercise is redundant with L01. Consider replacing L07's proof with something genuinely different (e.g., a non-constant summand like `∑ i ∈ range n, (i + 1)` by induction) so the Lean exercise is fresh even though the transfer conclusion remains.

### P3 (nice to have)

5. **Enrich L04 and L05** — These single-tactic levels are thin for a pset. Consider adding a follow-up step:
   - L04: After `sum_filter`, require simplifying or evaluating the conditional sum at a concrete value.
   - L05: After `sum_comm`, require factoring the result using `Finset.mul_sum` to show `(∑ f) * (∑ g)`.

---

## 11. What to Playtest After Patching

After implementing P1 and P2 fixes:

1. **Re-audit the new boss** for integration quality, exploit resistance, and proof length (should not exceed what was practiced by more than ~50%).
2. **Verify `DisabledTheorem` entries compile** and that the intended induction proofs still work.
3. **Re-simulate the novice path** through the redesigned boss to check for surprise burden.
4. **Check L07 replacement** (if L07 proof is changed) for coverage of T2 — the transfer conclusion must still make sense with the new proof.
