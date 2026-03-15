# W4 MultisetHierarchy -- Playtest Audit (Round 2)

## Overall verdict

**CONDITIONAL PASS.** The world has been substantially improved since R1. It grew from 9 to 14 levels, added genuine proof-move teaching (symbolic counting, reduce-then-compute pattern, cardinality inequality, Nodup connection), established a scaffold fade from computation to symbolic reasoning to integration, and redesigned the boss to require W4-specific proof moves. The R1 P0 issues (trivial everywhere, boss as gauntlet, no DisabledTactic lines) are all fixed.

Two issues prevent a clean pass:

1. **P1-1**: `norm_num` one-shots the boss and 7 other levels (L01, L05, L07, L10, L11, L13, L14). It is never disabled anywhere. This is the remaining single-tactic exploit path.
2. **P1-2**: Three hints direct the player to use `decide` on levels where `decide` is disabled (L07, L10, L14). The player will be told to use a tactic that the game rejects.

Both are fixable without restructuring. After those fixes, the world should pass R3 cleanly.

---

## Rubric scores

| Category | Score | R1 Score | Notes |
|----------|-------|----------|-------|
| 1. Coverage closure | 3 | 2 | `mem_coe`, `count_cons_self/of_ne`, `toFinset_card_le`, `coe_nodup`, `map_coe` all covered. Missing: `count_cons_of_ne` is documented but never exercised by the player. |
| 2. Granularity fit | 3 | 2 | 14 levels with clear dominant lessons. Some levels (L08, L09) remain pure computation, but they serve as contrast before the symbolic levels. |
| 3. Proof-move teaching | 3 | 1 | Major improvement. Reduce-then-compute named explicitly (L13). Symbolic counting (L07). General theorem application (L11). Still: no level requires `count_cons_of_ne` (the "different element" case). |
| 4. Inventory design | 3 | 2 | Good introduction cadence. `Finset.card` documented (L10). All major items have docs. |
| 5. Hint design and recoverability | 2 | 2 | Strategy hints added. But broken hints on L07/L10/L14 (say `decide` when it is disabled). No `Branch` hints for wrong moves. |
| 6. Demonstration -> practice -> transfer -> boss | 3 | 1 | Clear progression: computation (L01-L06) -> symbolic (L07) -> toFinset (L08-L09) -> hierarchy (L10) -> general (L11-L12) -> pattern naming (L13) -> boss (L14). |
| 7. Mathematical authenticity | 4 | 3 | Information-loss narrative is visceral (L04). Hierarchy table in L06. Nodup connection to W3 (L12). Reduce-then-compute named and transferred (L13). |
| 8. Paper-proof transfer | 3 | 2 | L13 explicitly connects reduce-then-compute to mathematical writing. L14 conclusion summarizes proof techniques. L11 distinguishes "verify by calculation" from "cite a theorem." |
| 9. Technical fit and maintainability | 3 | 1 | All levels have DisabledTactic lines. `trivial` disabled everywhere. `decide` disabled where intended. Build succeeds. Remaining issue: `norm_num` not disabled anywhere. |

**Average: 3.0** (meets the 3.0 threshold)
**Categories below 2: none**
**Categories at 2: one** (hint design)

---

## P0 issues (blocking)

None. All R1 P0 issues resolved.

---

## P1 issues (high)

### P1-1: `norm_num` one-shots 8 of 14 levels including the boss

**Severity**: P1 (high)
**Type**: Statement exploitability -- systemic

`norm_num` is not in any DisabledTactic line. It closes the following levels in one shot, completely bypassing the intended proof:

| Level | Intended proof | `norm_num` bypasses |
|-------|---------------|-------------------|
| L01 | `rfl` | Bypasses learning definitional equality |
| L05 | `rw [Multiset.card_map]; rfl` | Bypasses `card_map` |
| L07 | `rw [count_cons_self]; decide` | Bypasses symbolic counting entirely |
| L10 (both parts) | `constructor; rfl; decide` | Bypasses `constructor` + the dual-reasoning pattern |
| L11 | `exact Multiset.toFinset_card_le _` | Bypasses learning to cite a general theorem |
| L13 | `rw [map_coe]; rw [coe_eq_coe]; decide` | Bypasses the entire reduce-then-compute lesson |
| L14 (boss) | `constructor + card_map/map_coe/coe_eq_coe + toFinset_card_le` | One-shots the entire boss integration |

**Evidence** (all verified by `lake env lean`):
```lean
-- L07 (count symbolic -- the most pedagogically damaging):
example : Multiset.count 1 (1 ::ₘ (↑([2, 3] : List Nat) : Multiset Nat)) = 1 := by norm_num
-- L14 (boss -- complete bypass):
example :
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).card = 4 ∧
    Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat) = ↑([1, 2, 1, 3] : List Nat) ∧
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).toFinset.card ≤
    (Multiset.map (· + 1) (↑([0, 1, 0, 2] : List Nat) : Multiset Nat)).card := by norm_num
```

**Fix**: Add `norm_num` to the DisabledTactic line on levels where it bypasses the lesson: L01, L05, L07, L10, L11, L13, L14. (Levels L02, L03, L04, L06, L08, L09, L12 do not need it -- either `norm_num` fails on them or `decide` is already available and the lesson allows computation.)

Updated DisabledTactic lines:
- L01: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L05: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L07: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L10: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L11: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L13: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
- L14: `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`

Also add `TacticDoc norm_num` somewhere (e.g., L01 or whichever level first disables it):
```lean
/-- `norm_num` evaluates numerical expressions and can solve arithmetic goals automatically.
In this course, `norm_num` is sometimes disabled so that you practice structural proof
techniques rather than delegating everything to numerical computation. -/
TacticDoc norm_num
```

---

### P1-2: Three hints tell the player to use `decide` on levels where `decide` is disabled

**Severity**: P1 (high)
**Type**: Hint mismatch -- broken rescue path

The following levels have `decide` in their DisabledTactic line but their hints tell the player to use `decide`:

**L07** (line 59): Hint says "Try `decide`." after `rw [Multiset.count_cons_self]`.
- `decide` is disabled on L07.
- The player follows the hint, types `decide`, and gets a "tactic not available" error.
- **Fix**: Change the hint to "The remaining goal is a concrete equality. Try `rfl`." (Verified: `rfl` closes the goal after the `rw`.) Also change the author proof from `decide` to `rfl`.

**L10** (line 50): Hint says "Try `decide`." for the second conjunct.
- `decide` is disabled on L10.
- **Fix**: Change to "Try `rfl`. Even though `toFinset` involves deduplication, the result on this specific list is definitionally equal to `3`." Also change the author proof from `decide` to `rfl`.

**L14** (line 64, inside second conjunct): Author proof uses `decide` after `rw [Multiset.coe_eq_coe]`.
- `decide` is disabled on L14.
- After the two `rw` steps, the goal is `(List.map (· + 1) [0, 1, 0, 2]).Perm [1, 2, 1, 3]` which is definitionally true (`rfl` works).
- The hint says "then `decide`" -- broken.
- **Fix**: Change the hint and author proof to use `rfl` instead of `decide` for the permutation step.

---

## P2 issues (medium)

### P2-1: `rfl` one-shots L05, L07, L13, and boss conjuncts 1-2

**Severity**: P2 (medium)
**Type**: Statement exploitability -- unavoidable

`rfl` cannot be disabled. The following levels are closed by `rfl` alone, bypassing the intended rewrite steps:

| Level | Intended proof | `rfl` bypasses |
|-------|---------------|---------------|
| L05 | `rw [Multiset.card_map]; rfl` | The `rw` step is unnecessary; `rfl` works directly |
| L07 | `rw [count_cons_self]; rfl` | Same: `rfl` works without the `rw` |
| L13 | `rw [map_coe]; rw [coe_eq_coe]; decide` | `rfl` one-shots the whole thing |
| L14 conjuncts 1-2 | `rw [card_map]; rfl` and `rw [map_coe, coe_eq_coe]; decide` | Both close with `rfl` |

**Assessment**: Since `rfl` cannot be disabled, this is inherent to using concrete data in statements. Accept as P2. The hints guide the learner through the `rw` path, and a learner who uses `rfl` directly has still learned something (that the equality is definitional). The `rw` path is more instructive, but `rfl` is a valid proof.

**Mitigation** (optional, not required for pass): For L13 (the reduce-then-compute practice level), consider using data where `rfl` does NOT close the goal -- e.g., use lists that are not in the same order so `coe_eq_coe` + `decide` is genuinely required. Example:
```lean
-- Multiset.map (· * 2) ↑[1, 3, 2] = ↑[2, 4, 6]
-- After map_coe: ↑[2, 6, 4] = ↑[2, 4, 6]  -- NOT definitionally equal!
-- Requires coe_eq_coe + decide
```
This would make L13 non-trivially different from `rfl`.

---

### P2-2: `decide` one-shots L02, L03, L04, L12 -- bypassing rewrite lessons

**Severity**: P2 (medium)
**Type**: Statement exploitability -- per-level

On levels where `decide` is NOT disabled (L02, L03, L04, L12), `decide` alone closes the goal, bypassing the intended rewrite with a bridge lemma:

| Level | Intended proof | `decide` bypass |
|-------|---------------|----------------|
| L02 | `rw [Multiset.mem_coe]; decide` | `decide` alone: bypasses learning `mem_coe` |
| L03 | `rw [Multiset.coe_eq_coe]; decide` | `decide` alone: bypasses learning `coe_eq_coe` |
| L04 | `constructor; decide; rw [coe_eq_coe]; decide` | `decide` alone: bypasses both `constructor` and `coe_eq_coe` |
| L12 | `constructor; rw [coe_nodup]; decide; exact toFinset_val _` | `decide` alone: bypasses everything |

**Assessment**: This is a design choice. The levels are intended to teach the `rw [bridge_lemma]; decide` pattern, and `decide` is left available because it IS part of the proof (just used after the rewrite, not instead of it). The hints guide toward the two-step path. However, a learner who discovers `decide` works alone will skip the rewrite step.

**Recommendation**: Consider disabling `decide` on L02, L03, and L04, and changing the intended second step to `rfl` (which also works after the `rw` on L02 and L03, since the rewritten goals are decidable). Verify:
- L02 after `rw [mem_coe]`: goal is `2 ∈ [1, 2, 3]` -- `decide` or `rfl`? Need to check.
- L03 after `rw [coe_eq_coe]`: goal is `[1,2,3].Perm [3,1,2]` -- `decide` or `rfl`? Need to check.

For L04, `decide` should remain available for the first conjunct (the list inequality) since that IS the lesson. But the second conjunct's `rw` step is bypassed.

For L12, `decide` is needed for part 1 (`rw [coe_nodup]; decide`), so it cannot be fully disabled. Accept as P2.

---

### P2-3: No `Branch` hints for common wrong moves

**Severity**: P2 (medium)
**Type**: Hint design -- recoverability

No `Branch` hints exist in any of the 14 levels. This was flagged in R1 (P2-4) and was not addressed. Common wrong moves that would benefit from Branch rescue:

- **L02**: Learner tries `decide` directly (works, but misses the point). A Branch hint after `decide` could say "That works, but you missed learning `Multiset.mem_coe`. Try `rw [Multiset.mem_coe]` first next time."
- **L05**: Learner tries `rfl` directly (works). A Branch could say "That works because this equality is definitional. But try `rw [Multiset.card_map]; rfl` to see the structural reason."
- **L13**: Learner tries `rfl` (works). Same idea.

Note: Branch hints must contain complete proofs. A Branch that catches `decide` on L02 would need `decide` as the completing tactic, which means it technically works as a valid path. The pedagogical message goes in the hint text.

---

### P2-4: `count_cons_of_ne` documented but never exercised

**Severity**: P2 (medium)
**Type**: Coverage -- introduced but not practiced

L07 introduces both `count_cons_self` and `count_cons_of_ne` via `NewTheorem`. The level exercises `count_cons_self` (counting the matching element). But `count_cons_of_ne` (counting a non-matching element) is never used by the player in any level. It appears in docs only.

This is a weak coverage state: the theorem is introduced (I) but has no supported practice (S), retrieval (R), or integration (G).

**Fix options** (not blocking for R2 pass):
1. Add a sublevel or modify L07 to include a second step that requires `rw [Multiset.count_cons_of_ne h]` for a different element.
2. Use `count_cons_of_ne` in the boss (L14) as one of the required steps.
3. Accept as intentional: `count_cons_of_ne` is made available for reference but not tested because the world focuses on the matching case.

---

### P2-5: L12 is overbroad -- two unrelated lessons in one level

**Severity**: P2 (medium)
**Type**: Granularity

L12 (NodupConnection) teaches two distinct things:
1. Part 1: `Multiset.coe_nodup` -- the bridge between `List.Nodup` and `Multiset.Nodup`
2. Part 2: `Multiset.toFinset_val` -- the internal structure of finsets

These are conceptually different: part 1 is about the `Nodup` property across the hierarchy, while part 2 is about the `toFinset`/`dedup` relationship. A learner could fail on part 2 while understanding part 1 perfectly, and vice versa.

**Fix** (optional): Split L12 into two levels. However, since each part is short (one `rw` + `decide`, one `exact`), merging them is defensible as a "consolidation" level that ties two threads together. Accept as P2.

---

## P3 issues (low)

### P3-1: Build info messages about missing TacticDoc on L14

The build produces info-level messages about missing TacticDoc for `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` on L14. These are info, not warnings -- the game server finds existing docstrings from earlier levels. No action needed, but adding `norm_num` to DisabledTactic (per P1-1) will also require a `TacticDoc norm_num` somewhere before L14.

### P3-2: L01 disables `decide` but the lesson is `rfl` -- acceptable but unusual

L01's lesson is `rfl`. Disabling `decide` is correct (prevents the learner from using `decide` instead of `rfl`), but a novice might try `decide` first (since they learned it in W2) and be confused by the error. The strategy hint guides toward `rfl`, so the rescue path exists. No action needed.

---

## Coverage analysis

### Coverage states for key items:

| Item | Axis | States | Notes |
|------|------|--------|-------|
| `Multiset` | MATH | I(L01), S(L02-L14) | Well covered |
| `Multiset.card` | MATH | I(L01), S(L05,L10), G(L14) | Good |
| `Multiset.mem_coe` | MOVE | I(L02), S(implied), G(boss via understanding) | Introduced and used |
| `Multiset.coe_eq_coe` | MOVE | I(L03), S(L04,L13), G(L14) | Well covered |
| `List.Perm` | MATH | I(L03), S(L04) | Adequate |
| `Multiset.map` | MATH | I(L05), S(L13), G(L14) | Good |
| `Multiset.card_map` | MOVE | I(L05), G(L14) | Missing explicit S (supported practice) |
| `Multiset.count` | MATH | I(L06), S(L07) | Good |
| `count_cons_self` | MOVE | I(L07) | **Missing S, R, G** -- only exercised once |
| `count_cons_of_ne` | MOVE | I(L07 doc) | **Never exercised** -- doc only |
| `Multiset.toFinset` | MATH | I(L08), S(L09,L10), G(L14) | Good |
| `List.toFinset` | MATH | I(L09) | Used once |
| `Finset.card` | MATH | I(L10), S(L11), G(L14) | Good |
| `toFinset_card_le` | MOVE | I(L11), G(L14) | Good integration |
| `Multiset.Nodup` | MATH | I(L12) | Single introduction |
| `Multiset.dedup` | MATH | I(L12) | Single introduction |
| `coe_nodup` | MOVE | I(L12) | Single use |
| `toFinset_val` | MOVE | I(L12) | Single use |
| `map_coe` | MOVE | I(L13), G(L14) | Good |
| Reduce-then-compute | MOVE+TRANSFER | I(L02-L03 implicit), Named(L13), G(L14) | **Well done** -- named strategy with transfer |
| Information loss | MATH+TRANSFER | I(L04 lists), S(L09 finsets), G(L10) | **Well done** -- visceral demonstration |

### Coverage gaps:
1. `count_cons_of_ne` -- introduced in doc, never used (P2-4)
2. `count_cons_self` -- used once, no retrieval or integration
3. `Multiset.Nodup` and `Multiset.dedup` -- each used once, no retrieval

### Coverage strengths:
1. Reduce-then-compute named and transferred (excellent)
2. Information loss demonstrated viscerally at both layers (excellent)
3. W3 connection via `coe_nodup` (good cross-world continuity)
4. `toFinset_card_le` properly seeded before boss integration

---

## Granularity analysis

### Level-by-level dominant lessons:

| Level | Role | Dominant lesson | Clear? |
|-------|------|----------------|--------|
| L01 | First contact | Multiset coercion, rfl for definitional equality | Yes |
| L02 | First contact | `mem_coe` bridge lemma | Yes |
| L03 | First contact | `coe_eq_coe` bridge lemma, reduce-then-compute intro | Yes |
| L04 | Practice + contrast | Information loss for lists (conjunction) | Yes |
| L05 | First contact | `Multiset.map` and `card_map` | Yes |
| L06 | First contact | `Multiset.count`, concrete computation | Yes |
| L07 | First contact | `count_cons_self`, symbolic reasoning | Yes |
| L08 | First contact | `Multiset.toFinset` | Yes |
| L09 | Practice + contrast | Information loss for finsets | Yes |
| L10 | Integration | Three-layer hierarchy comparison | Yes |
| L11 | First contact | General theorem application (`toFinset_card_le`) | Yes |
| L12 | Integration + cross-world | `Nodup` connection, `toFinset_val` | Borderline (two topics) |
| L13 | Transfer | Named proof strategy (reduce-then-compute) | Yes |
| L14 | Boss | Integration of card_map, map_coe, coe_eq_coe, toFinset_card_le | Yes |

### Scaffold fade assessment:
- L01-L06: Heavy scaffolding, concrete computation, `decide`/`rfl` dominant
- L07: Transition to symbolic reasoning (`rw` + structural lemma)
- L08-L09: Return to computation but with new concepts
- L10: Integration of prior concepts
- L11: Abstract reasoning (general theorem application)
- L12: Cross-world connection (W3 callback)
- L13: Named strategy (meta-level)
- L14: Boss integration

This is a genuine gradient. **Improvement over R1**: significant.

---

## Learner simulation

### Attentive novice

**Path through the world**: The novice reads each introduction, follows the hints, and builds understanding of the List-Multiset-Finset hierarchy.

**First likely stuck point**: L07 (CountSymbolic). The novice must use `rw [Multiset.count_cons_self]`, which is a new lemma applied in a new way. The strategy hint ("Which count lemma handles the case where the element being counted matches the head?") gives good direction, but the novice might not immediately recognize which lemma applies. The hidden hint provides the answer.

**CRITICAL**: After the `rw`, the hint says "Try `decide`" -- but `decide` is disabled! The novice will be stuck. They need to discover `rfl` on their own. **This is the P1-2 bug in action.**

**Second stuck point**: L11 (CardinalityInequality). The novice must use `exact Multiset.toFinset_card_le _` -- their first time using a general theorem with `exact` and an underscore argument. The intro explains this well, and the hint provides the exact syntax. Should be recoverable.

**Third stuck point**: L14 (Boss). The novice must plan a multi-step proof with 3 conjuncts, choosing the right technique for each. If they read the introduction (which explains what each part requires), they have a roadmap. Hints cover all stuck points.

**Lesson legibility**: The novice exits knowing:
1. What multisets are and how they relate to lists and finsets
2. The reduce-then-compute proof pattern (named!)
3. How to use bridge lemmas to convert between types
4. That information is lost at each step of the hierarchy
5. That general theorems can be applied to specific instances

This is a substantial upgrade from R1.

**Remaining risk**: If the novice discovers `norm_num` (which is available), they can skip most lessons. But `norm_num` is less likely to be tried than `decide` or `trivial`, since it's typically associated with numeric goals, not multiset goals.

### Experienced Lean user

**Path through the world**: The experienced user will likely try `decide` on each level. On levels where it works (L02, L03, L04, L06, L08, L09, L12), they pass quickly. On levels where it's disabled (L01, L05, L07, L10, L11, L13, L14), they notice.

**Key exploit**: `norm_num` closes 8 levels. An experienced user who knows `norm_num` can bypass most of the world. This is the P1-1 issue.

**`rfl` exploit**: Levels L05, L07, L13 are one-shot by `rfl`. An experienced user will try this.

**Overall friction**: Moderate. The symbolic levels (L07, L11, L13) provide genuine engagement even for an experienced user, assuming `norm_num` is disabled. The boss requires choosing the right approach for each conjunct, which is reasonable.

**Avoidable friction**: None. The proofs are appropriately concise.

**Alias gaps**: None significant. Standard tactic names are used throughout.

---

## Boss integrity check (L14)

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | PASS | `card_map` (L05), `map_coe` (L13), `coe_eq_coe` (L03), `toFinset_card_le` (L11) all seeded before boss |
| Closure quality | PASS | Every proof move in the boss was taught and practiced in earlier levels |
| Integration quality | PASS | Three conjuncts require three different techniques. Not a gauntlet -- the learner must choose the right approach for each part. The `map_coe` + `coe_eq_coe` + `decide` chain in conjunct 2 is a genuine multi-step reduction. |
| Surprise burden | NONE | No new material. Different list from practice levels ([0,1,0,2] vs previous examples). |
| Can learner explain proof? | YES | "I split the conjunction. For cardinality, I used card_map to remove the map. For the multiset equality, I pushed the map inside the coercion and reduced to a permutation. For the inequality, I cited the general theorem." |

**Verdict**: The boss passes the integration test. It is no longer a gauntlet. **Major improvement from R1.**

**Remaining concern**: `norm_num` one-shots the entire boss (P1-1). After `norm_num` is disabled, the boss will properly require the intended multi-step proof.

Also: boss conjuncts 1-2 close with `rfl` (P2-1), which means only conjunct 3 (`toFinset_card_le`) truly forces a non-trivial step. After `norm_num` is disabled, the learner can do `constructor; rfl; constructor; rfl; exact Multiset.toFinset_card_le _`. This is still integration (they must use `constructor` and `exact` with a named theorem), but the `rw` steps are not forced. Accept as P2 since `rfl` is undisableable.

---

## Course-role sanity

**Intended role**: Lecture world
**Actual role**: Lecture world with good proof-move teaching

**Verdict**: PASS. The world now genuinely functions as a lecture world. It teaches definitions alongside proof moves, names a reusable proof strategy, demonstrates information loss viscerally, and has a boss that integrates multiple techniques. The R1 verdict of "definition tour" no longer applies.

---

## Comparison with R1

| R1 Issue | Status | Notes |
|----------|--------|-------|
| P0-1: `trivial` closes all levels | FIXED | `trivial` disabled on all 14 levels |
| P0-2: `decide` closes non-decide levels | FIXED | `decide` disabled on L01, L05, L07, L10, L11, L13, L14 |
| P0-3: `aesop` closes boss | FIXED | `aesop` disabled on all levels |
| P0-4: Boss is a gauntlet | FIXED | Redesigned with 3 distinct proof techniques |
| P1-1: No new proof moves | FIXED | Symbolic counting (L07), general theorem (L11), named pattern (L13) |
| P1-2: `Multiset.mem` missing | FIXED | L02 introduces `mem_coe` |
| P1-3: No scaffold fade | FIXED | Clear gradient from computation to symbolic to integration |
| P2-1: L08 exploitable by `rfl` | ADDRESSED | L08 now uses `decide` (which is allowed); `rfl` issue is different level (L12 part 2) |
| P2-2: `Finset.card` undocumented | FIXED | L10 introduces `Finset.card` with `NewDefinition` |
| P2-3: Hints too direct | PARTIALLY FIXED | Strategy hints added, but still no Branch hints |
| P2-4: No Branch hints | NOT FIXED | Still no Branch hints anywhere |
| P2-5: Non-injectivity transfer | PARTIALLY FIXED | L09 conclusion connects to non-injectivity better |

---

## Ranked patch list

| Priority | Issue | Fix | Files affected |
|----------|-------|-----|---------------|
| 1 | P1-1: `norm_num` one-shots 8 levels | Add `norm_num` to DisabledTactic on L01, L05, L07, L10, L11, L13, L14. Add `TacticDoc norm_num` to L01 (before DisabledTactic). | L01, L05, L07, L10, L11, L13, L14 |
| 2 | P1-2: Hints say `decide` on levels where it is disabled | L07 line 59: change "Try `decide`" to "Try `rfl`"; change author proof `decide` to `rfl`. L10 line 50: same. L14 line 64: change hint and author proof from `decide` to `rfl`. | L07, L10, L14 |
| 3 | P2-3: No Branch hints | Add Branch hints for common wrong moves on at least L02 (decide one-shot), L05 (rfl one-shot), L13 (rfl one-shot). | L02, L05, L13 |
| 4 | P2-4: `count_cons_of_ne` never exercised | Consider adding a sublevel to L07 or a new level exercising the non-matching case. Or integrate into boss. | L07 or new file |
| 5 | P2-1: `rfl` one-shots L05, L07, L13 | Consider using non-definitionally-equal data in L13 (e.g., `↑[1,3,2]` instead of `↑[1,2,3]` so the mapped result needs `coe_eq_coe`). | L13 |

---

## What to playtest again after patching

1. **All levels with `norm_num` added to DisabledTactic**: Verify `norm_num` is rejected. Verify the intended proof still works. Verify `omega` also fails (it should, based on R2 testing).

2. **L07, L10, L14 hint fixes**: Verify the hint path works end-to-end with the corrected tactic names. Ensure `rfl` closes the post-`rw` goals as expected.

3. **Build**: `lake build` after all patches. Check for new TacticDoc warnings from `norm_num` in DisabledTactic.

4. **Boss re-test**: After `norm_num` disabled, verify:
   - `norm_num` is rejected
   - `rfl` still works on conjuncts 1-2 (acceptable P2)
   - `exact Multiset.toFinset_card_le _` required for conjunct 3
   - The intended full proof path works: `constructor; rw [card_map]; rfl; constructor; rw [map_coe, coe_eq_coe]; rfl; exact toFinset_card_le _`

5. **Optional L13 redesign**: If L13's data is changed to make `rfl` fail, verify the new proof path and update hints accordingly.
