# W4 MultisetHierarchy -- Playtest Audit (Round 3)

## Overall verdict

**NOT PASSING.** The R2 fixes (disabling `norm_num` on L07, disabling `omega` on L11) are confirmed correct and effective. However, a systemic `norm_num` exploit remains: `norm_num` is NOT disabled on 12 of the 14 levels, and it one-shots **8 levels** including the boss (L14). On levels where `decide` was already disabled to force symbolic reasoning (L05, L10, L13, L14), `norm_num` provides an equivalent bypass. The boss can be completed with `constructor; norm_num; constructor; norm_num; norm_num` -- no W4-specific proof move is required.

A secondary issue: `decide` is available on L02, L03, L04, and L12, where it one-shots the goal and bypasses the intended bridge-lemma lessons (`mem_coe`, `coe_eq_coe`, `coe_nodup`, `toFinset_val`).

A third issue: L07's hint says "Try `decide`" but `decide` is disabled on L07 (added in R2). The player cannot follow the hint. The valid proof `rw [count_cons_self]; rfl` works but is not hinted.

The world's narrative, proof-move structure, and boss design are all strong -- the R1 rewrite addressed all structural issues effectively. The remaining problems are tactic-gating and one hint/tactic mismatch.

---

## R2 fix verification

| R2 fix | Verified? | Notes |
|--------|-----------|-------|
| L07: `norm_num` added to DisabledTactic | YES | `norm_num` no longer closes L07. Only `rw [count_cons_self]; decide` works (and `decide` is already disabled, so learner must rw + raw computation). Confirmed: `omega` also fails on L07. |
| L11: `omega` added to DisabledTactic | YES | `omega` no longer closes L11. Intended proof `exact Multiset.toFinset_card_le _` is forced... **except** `norm_num` closes L11 (see P0-1 below). |

---

## Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Solid: mem_coe, coe_eq_coe, card_map, count_cons_self, toFinset, toFinset_card_le, coe_nodup, toFinset_val, map_coe all covered with introduction + practice. Reduce-then-compute named as proof strategy. |
| 2. Granularity fit | 3 | Each level has one dominant lesson. Good progression from concrete (L01-L06) to symbolic (L07) to hierarchy (L08-L12) to strategy-naming (L13) to integration (L14). |
| 3. Proof-move teaching | 3 | Three distinct proof moves: reduce-then-compute (rw + decide/rfl), derive-then-instantiate (exact lemma _), and symbolic counting (count_cons_self). Major R1 improvement. |
| 4. Inventory design | 3 | Good: NewDefinition/NewTheorem at appropriate moments. Finset.card introduced in L10. TacticDoc entries present for disabled tactics. Minor: missing TacticDoc for `simp`, `aesop`, `simp_all` in L14 (build warnings). |
| 5. Hint design and recoverability | 3 | Strategy-level hints precede direct-answer hints on all levels. Layered approach: "What type of proof is this?" -> "Try `rw [specific_lemma]`". No Branch hints for wrong moves (P2). |
| 6. Worked example -> practice -> transfer -> boss | 3 | Clear gradient: concrete computation (L01-L06) -> symbolic reasoning (L07) -> hierarchy traversal (L08-L12) -> named strategy (L13) -> integration boss (L14). Boss requires 3 distinct proof techniques. |
| 7. Mathematical authenticity | 4 | Excellent prose. Hierarchy table in L06. Information-loss demonstrated concretely in L04 and L09. Transfer moments in conclusions. The reduce-then-compute naming in L13 is pedagogically strong. |
| 8. Paper-proof transfer | 3 | L13 explicitly names the proof strategy and connects to mathematical writing ("By [theorem], this reduces to [simpler statement]"). L11 teaches the derive-then-instantiate pattern. Conclusions have "In plain language" summaries. |
| 9. Technical fit and maintainability | 2 | **Needs revision.** `norm_num` exploit on 8 levels (P0-1). `decide` exploit on 4 levels (P1-1). Build warnings about missing TacticDoc (P2-3). |

**Average: 3.0** (meets threshold)
**Categories below 2: none**
**Categories at 2: one** (technical fit -- due to norm_num exploit)

The world meets the structural quality bar but is blocked by tactic-gating issues.

---

## P0 issues (blocking)

### P0-1: `norm_num` one-shots 8 levels including the boss

**Severity**: P0 (blocking)
**Type**: Statement exploitability -- systemic

`norm_num` is not in the `DisabledTactic` line for 12 of 14 levels (only L07 disables it). On 8 of those 12, `norm_num` closes the goal entirely:

| Level | Intended proof | `norm_num` closes? | Bypass severity |
|-------|---------------|-------------------|----------------|
| L01 | `rfl` | YES | Low (both teach definitional equality) |
| L02 | `rw [mem_coe]; decide` | YES | **High** -- bypasses `mem_coe` |
| L05 | `rw [card_map]; rfl` | YES | **High** -- bypasses `card_map` |
| L06 | `decide` | YES | Low (both are computation) |
| L10 | `constructor; rfl; decide` | YES (one-shot, no constructor needed) | **High** -- bypasses constructor + both proof moves |
| L11 | `exact toFinset_card_le _` | YES | **Critical** -- bypasses the general-theorem proof move entirely |
| L13 | `rw [map_coe, coe_eq_coe]; decide` | YES | **High** -- bypasses both bridge lemmas |
| L14 | Three-part proof with card_map, map_coe, coe_eq_coe, toFinset_card_le | YES (`constructor; norm_num; constructor; norm_num; norm_num`) | **Critical** -- bypasses entire boss integration |

The critical bypasses are L05, L10, L11, L13, L14 -- levels where `decide` was explicitly disabled to force the learner to use bridge lemmas, but `norm_num` provides the same computational power as `decide`.

**Fix**: Add `norm_num` to `DisabledTactic` on levels where it bypasses the intended lesson:
- L01: Add `norm_num` (minor, but consistent)
- L02: Add `norm_num` (bypasses mem_coe)
- L05: Add `norm_num` (already has decide disabled; norm_num is equivalent bypass)
- L10: Add `norm_num` (bypasses constructor + both proof moves)
- L11: Add `norm_num` (bypasses exact toFinset_card_le)
- L13: Add `norm_num` (bypasses map_coe + coe_eq_coe)
- L14: Add `norm_num` (bypasses entire boss)

Levels where `norm_num` fails naturally (L03, L04, L08, L09) or where `decide` is already intended and available (L06, L08, L09): no change needed.

Recommendation: add `norm_num` to the standard disabled set for this world. The standard set should be `trivial decide native_decide simp aesop simp_all norm_num` for levels where `decide` is disabled, and `trivial native_decide simp aesop simp_all norm_num` for levels where `decide` is intentionally available.

---

## P1 issues (high)

### P1-1: `decide` one-shots L02, L03, L04, L12 -- bypassing bridge-lemma lessons

**Severity**: P1 (high)
**Type**: Statement exploitability -- per-level

`decide` is available (not disabled) on L02, L03, L04, L06, L08, L09, L12. On L06, L08, L09, `decide` is the intended tactic (or part of the intended proof). But on L02, L03, L04, and L12, `decide` alone bypasses the dominant lesson:

| Level | Intended lesson | decide bypass |
|-------|----------------|---------------|
| L02 | Learn `Multiset.mem_coe` as bridge lemma | `decide` closes `2 ∈ ↑[1,2,3]` without rw |
| L03 | Learn `Multiset.coe_eq_coe` as bridge lemma | `decide` closes `↑[1,2,3] = ↑[3,1,2]` without rw |
| L04 | Learn `constructor` + bridge lemma in conjunction | `decide` closes entire conjunction without constructor or rw |
| L12 | Learn `Multiset.coe_nodup` + `Multiset.toFinset_val` | `decide` closes both parts without rw or exact |

This is problematic because:
- L02 and L03 are **first-contact levels** for their respective bridge lemmas. If the learner bypasses them with `decide`, they never learn the bridge lemma.
- L12 combines two new lemmas; bypassing both with `decide` means neither is learned.

**Fix**: Disable `decide` on L02, L03, L04, and L12. These levels already use `decide` as part of the intended proof (after `rw`), but the `rw` step is the dominant lesson, and `decide` should only be available for the computational cleanup step -- not as a one-shot bypass.

**Implementation note**: If `decide` is disabled globally on these levels, the intended proof `rw [mem_coe]; decide` breaks. There are two options:
1. **Change the intended proof** to `rw [mem_coe]; rfl` or `rw [mem_coe]` followed by a tactic that is not disabled. Check if `rfl` closes the post-rw goal.
2. **Keep `decide` available** but accept the bypass (P1, not P0). The hints strongly guide the learner toward the bridge lemma, and a learner who uses `decide` directly at least learns that `decide` works on multiset propositions.

Let me assess option 2: the levels' hints say "What lemma converts multiset membership to list membership?" -- a learner following hints would learn the bridge lemma. A learner who ignores hints and uses `decide` is choosing to skip the lesson. This is an informed choice, not an accidental bypass. **Recommend: accept as P2 for L02/L03, P1 for L04/L12 (where multiple lessons are bypassed).**

---

### P1-2: L07 hint recommends disabled tactic `decide`

**Severity**: P1 (high)
**Type**: Hint/tactic mismatch (failure taxonomy #7)

L07's second post-rw hint says: "Since `1` does not appear in `[2, 3]`, the count is `0`, so this becomes `0 + 1 = 1`. Try `decide`."

But `decide` is disabled on L07 (added in R2 along with `norm_num`). The player cannot use `decide`. The valid proof path after `rw [count_cons_self]` is `rfl` (confirmed: the post-rw goal `(↑[2, 3]).count 1 + 1 = 1` is definitionally true because `Multiset.count 1 ↑[2, 3]` reduces to `0`).

**Fix**: Change the hint from "Try `decide`" to "Try `rfl`. The expression `(↑[2, 3]).count 1` reduces to `0`, making the goal `0 + 1 = 1`, which is definitional."

Also update the Statement proof itself from `decide` to `rfl` for consistency (both compile, but the Statement should match the player's expected path).

---

## P2 issues (medium)

### P2-1: Missing TacticDoc warnings in L14

**Severity**: P2 (medium)
**Type**: Build warning -- missing docs

The build outputs:
```
Game/Levels/MultisetHierarchy/L14_Boss.lean:125:44: Missing Tactic Documentation. Add simp
Game/Levels/MultisetHierarchy/L14_Boss.lean:125:49: Missing Tactic Documentation. Add aesop
Game/Levels/MultisetHierarchy/L14_Boss.lean:125:55: Missing Tactic Documentation. Add simp_all
```

`TacticDoc simp`, `TacticDoc aesop`, and `TacticDoc simp_all` are defined in L01, which imports before L14. However, the build system may not propagate TacticDoc across files in the same world (it may require them in the same file or prior via imports).

**Fix**: Add `TacticDoc simp`, `TacticDoc aesop`, `TacticDoc simp_all` entries to L14 (or verify that the import chain from L01 propagates to L14 -- if the world file lists L01 before L14, the docs should propagate).

Actually, from the build output, the warnings appear specifically for L14. Since L01 already defines `TacticDoc trivial`, `TacticDoc native_decide`, `TacticDoc aesop`, and `TacticDoc simp_all`, and the world file imports L01 before L14, the docs should propagate. The warnings may be spurious, or the missing docs are `simp` specifically (which may not have a TacticDoc entry anywhere).

**Fix**: Add `TacticDoc simp` to L01 (or any earlier level).

### P2-2: L12 part 2 exploitable by `rfl`

**Severity**: P2 (medium)
**Type**: Statement exploitability -- minor

`(Multiset.toFinset m).val = Multiset.dedup m` is definitionally true. `rfl` closes part 2 of L12, bypassing the intended `exact Multiset.toFinset_val _`. Both proofs teach the same concept (the equality holds by definition), so this is acceptable. The intended proof teaches the named lemma; `rfl` teaches that it is definitional. Either is valid.

**Fix**: Accept. No change needed.

### P2-3: No `Branch` hints for common wrong moves

**Severity**: P2 (medium)
**Type**: Hint design -- recoverability

No level in the world uses `Branch` hints. Common wrong moves that lack rescue:
- L02: Learner tries `rfl` (fails because multiset membership is not definitional)
- L05: Learner tries `rfl` directly (fails because `card_map` not applied yet)
- L07: Learner tries `decide` (disabled -- no hint explaining why)
- L11: Learner tries `decide` (disabled -- no hint explaining why)
- L13: Learner tries `rfl` or `decide` (both fail/disabled)

**Fix**: Add `Branch` hints for at least L07 and L11 where disabled tactics would be the learner's first instinct. Example for L07:
```
Branch
  Hint "The `decide` tactic is disabled here. The goal is to practice symbolic reasoning about `count` using rewriting lemmas, not to let the computer evaluate the answer."
```

### P2-4: `decide` on L04 bypasses `constructor` lesson in this context

**Severity**: P2 (medium, downgraded from P1)
**Type**: Statement exploitability

`decide` one-shots the conjunction in L04, bypassing `constructor`. However, `constructor` was already taught in earlier worlds, and L04's dominant lesson is "information loss" (a conceptual lesson), not `constructor`. The learner who uses `decide` still sees the statement and conclusion about information loss.

**Fix**: Accept at P2 severity. The conceptual lesson is in the prose; the proof mechanics are secondary here.

---

## Learner simulation

### Attentive novice

**First likely stuck point**: L07 (CountSymbolic). This is the first level where both `decide` and `norm_num` are disabled, forcing the learner to use `rw [Multiset.count_cons_self]`. The learner must read the introduction, find the lemma, and use it. The hints guide well: "Which count lemma handles the case where the element being counted matches the head?" followed by "Use `rw [Multiset.count_cons_self]`."

**Most likely wrong move**: In L05, trying `rfl` before `rw [Multiset.card_map]`. The goal `Multiset.card (Multiset.map ...) = 3` does NOT reduce by `rfl` because `card_map` is a propositional equality, not definitional. The hint covers this: "What lemma relates the cardinality of a mapped multiset to the cardinality of the original?"

**Hints rescue well?** Yes -- the two-layer hint design (strategy then code) is effective. The novice who reads the first hint gets oriented; the novice who is still stuck can reveal the hidden hint for the exact tactic.

**Lesson legibility**: Strong for L01-L10. The narrative builds clearly: coerce list -> check membership -> check equality -> observe information loss -> map -> count -> count symbolically -> convert to finset -> observe finset information loss -> compare cardinalities. The reduce-then-compute naming in L13 is a genuine pedagogical contribution.

**Risk**: If `norm_num` is not disabled, a novice who discovers it (perhaps from online resources or experimentation) can bypass L05, L10, L11, L13, and L14 entirely. This is the same risk profile as the `trivial` exploit from R1, just with a less obvious tactic.

### Experienced Lean user

**Avoidable friction**: Minimal. The levels are well-scoped. An experienced user would complete each in one or two steps.

**`norm_num` exploit**: An experienced user who knows `norm_num` would use it on every available level. They would complete the boss in 30 seconds with `constructor; norm_num; constructor; norm_num; norm_num`. This bypasses every W4-specific proof move and teaches nothing.

**Alias gaps**: None observed. The intended proof paths use standard Lean/mathlib idioms.

**Inventory clutter**: Well-managed. New items are introduced at natural moments.

---

## Boss integrity check (L14)

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | PASS | `card_map` (L05), `map_coe` + `coe_eq_coe` (L03, L13), `toFinset_card_le` (L11), `constructor` (W1+L04+L10) -- all seeded and practiced |
| Closure quality | PASS | Every lemma used in the boss was introduced and practiced in earlier levels |
| Integration quality | PASS (structurally) | Three distinct proof techniques required. Part 2 chains two rewrites (map_coe then coe_eq_coe) -- genuine integration. Part 3 uses a general theorem, not computation. **BUT** `norm_num` bypasses all integration. |
| Surprise burden | NONE | No new material. All moves practiced earlier. |
| Can learner explain proof? | YES | "Part 1: mapping preserves cardinality. Part 2: the mapped list is a permutation of [1,2,1,3]. Part 3: finset cardinality is at most multiset cardinality." |

**Boss verdict**: The boss design is excellent (no longer a gauntlet -- genuine integration with three distinct proof techniques). However, the `norm_num` exploit undermines it. Fixing P0-1 makes this boss genuinely strong.

---

## Coverage gaps

None significant. The world covers:
- Multiset definition and coercion (L01)
- Membership bridge (L02)
- Equality bridge (L03)
- Information loss at list->multiset level (L04)
- Map and cardinality preservation (L05)
- Count computation (L06)
- Count symbolic reasoning (L07)
- toFinset conversion (L08)
- Information loss at list->finset level (L09)
- Three-layer hierarchy comparison (L10)
- Cardinality inequality (L11)
- Nodup and dedup connection to W3 (L12)
- Named proof strategy: reduce-then-compute (L13)
- Integration boss (L14)

All five coverage layers addressed:
- **Syllabus**: Multiset as quotient, hierarchy List > Multiset > Finset
- **Proof-move**: reduce-then-compute, derive-then-instantiate, symbolic counting
- **Lean-expression**: rw with bridge lemmas, exact with _, decide for concrete checks
- **Example**: [1,2,3], [1,2,1,3], [0,1,0,2] as running examples
- **Transfer**: "In plain language" sections in every conclusion; L13 names the strategy explicitly

---

## Granularity defects

None significant. 14 levels for this content is appropriate -- the world covers a substantial topic (the three-layer hierarchy) with multiple proof techniques. The progression is well-structured:

- L01-L06: Concrete computation phase (one new concept per level)
- L07: Symbolic reasoning pivot
- L08-L12: Hierarchy traversal and cross-world connections
- L13: Strategy consolidation
- L14: Integration boss

No world-splitting trigger present: all content is thematically coherent (the List -> Multiset -> Finset hierarchy) and uses a single proof-pattern family (reduce-then-compute).

---

## Course-role sanity

**Intended role**: Lecture world
**Actual role**: Lecture world (confirmed)

The world teaches definitions AND proof moves (not just a definition tour). The reduce-then-compute pattern is a genuine transferable proof strategy. The boss requires integration, not just concatenation. This is a proper lecture world.

---

## Technical risks

1. **`norm_num` exploit (P0-1)**: The primary risk. Must be fixed before the world is considered complete.
2. **Build warnings (P2-1)**: Missing TacticDoc for `simp` in L14. Cosmetic but should be fixed.
3. **`decide` bypasses on bridge-lemma levels (P1-1)**: Design tension between leaving `decide` available for the intended proof's second step and preventing it from one-shotting the goal. Acceptable at P2 if the learner is guided by hints.

---

## Ranked patch list

| Priority | Issue | Fix | Files affected |
|----------|-------|-----|---------------|
| 1 | P0-1: `norm_num` one-shots 8 levels including boss | Add `norm_num` to `DisabledTactic` on L01, L02, L05, L10, L11, L13, L14. Consider also L04, L06, L12 for consistency. | L01, L02, L04, L05, L06, L10, L11, L12, L13, L14 |
| 2 | P1-2: L07 hint says "Try `decide`" but decide is disabled | Change hint to "Try `rfl`". Change Statement proof from `decide` to `rfl`. | L07 |
| 3 | P1-1: `decide` one-shots L02, L03, L04, L12 bypassing bridge lemmas | Accept as design choice (hints guide toward bridge lemma) OR disable `decide` on L02, L03, L04, L12 and change intended proof's `decide` step to `rfl` or verify `rfl` closes post-rw goal | L02, L03, L04, L12 |
| 4 | P2-1: Missing `TacticDoc simp` | Add `TacticDoc simp` to L01 | L01 |
| 5 | P2-3: No `Branch` hints | Add `Branch` hints for disabled-tactic confusion on L07, L11 | L07, L11 |

---

## What to playtest again after patching

1. **All levels with `norm_num` added to DisabledTactic**: Verify the intended proof still works after adding `norm_num` to the disabled list. Specifically check that no intended proof step uses `norm_num`.

2. **L07**: **CONFIRMED**: `rfl` closes the post-rw goal `(↑[2, 3]).count 1 + 1 = 1`. The valid player proof path is `rw [count_cons_self]; rfl`. After fixing P1-2 (changing the hint from "Try `decide`" to "Try `rfl`" and changing the Statement proof to use `rfl`), re-verify that the level works end-to-end.

3. **Boss (L14)**: After adding `norm_num` to DisabledTactic, verify the boss is not closeable by any remaining automation.

4. **Build**: `lake build` after all patches.
