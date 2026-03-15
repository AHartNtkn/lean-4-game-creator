# W4 MultisetHierarchy -- Playtest Audit (Round 1)

## Overall verdict

**NOT PASSING.** The world has a clear narrative and well-written prose, but it has severe exploitability problems and weak proof-move teaching. Every single level (all 9) can be closed by `trivial`, and most can also be closed by `decide` even where `decide` is not the intended tactic. The boss is a gauntlet of `constructor + decide/rfl` with no integration demand beyond what W1 already taught. The world introduces 8 new definitions/theorems but teaches zero new proof moves -- every intended proof uses only tactics introduced in W1-W2 (`rfl`, `decide`, `constructor`, `exact`, `rw`). This is a definition tour, not a lecture world.

---

## Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Definitions introduced but proof-move layer is empty; no `Multiset.mem`; no symbolic reasoning about `count` |
| 2. Granularity fit | 2 | Individual levels are well-scoped, but too many levels have the same dominant lesson ("`decide` on a concrete computation") |
| 3. Proof-move teaching | 1 | **Serious problem.** No new proof move is taught. Every level uses only `rfl`, `decide`, `constructor`, `rw`, or `exact` -- all from prior worlds |
| 4. Inventory design | 2 | Definitions introduced at good moments, but no `NewTactic` at all; no `DisabledTactic` lines; `Multiset.mem`/`mem_coe` missing |
| 5. Hint design and recoverability | 2 | Hints are correct but trivial (they just say "Try `decide`" or "Try `rfl`"); no rescue paths for wrong moves |
| 6. Demonstration -> practice -> transfer -> boss | 1 | **Serious problem.** No scaffold fade. Every level is at the same difficulty (one-shot by `decide` or `rfl`). Boss is a gauntlet, not an integration |
| 7. Mathematical authenticity | 3 | Good prose, good "plain language" summaries, good hierarchy table in L04 |
| 8. Paper-proof transfer | 2 | Transfer moments mentioned in prose but never exercised in proofs; the learner never writes a proof that mirrors mathematical reasoning |
| 9. Technical fit and maintainability | 1 | **Serious problem.** `trivial` closes all 9 levels; `decide` closes 7/9 levels including those where it is not intended; no `DisabledTactic` lines at all |

**Average: 1.78** (below the 3.0 threshold for "good")
**Categories below 2: three** (proof-move teaching, demonstration->boss, technical fit)

---

## P0 issues (blocking)

### P0-1: `trivial` closes ALL 9 levels

**Severity**: P0 (blocking)
**Type**: Statement exploitability -- systemic
**Details**: The `trivial` tactic closes every single level in the world. This was the same systemic issue found in W3_ex. No `DisabledTactic` line exists in any file.

**Evidence**:
```lean
-- Every one of these compiles:
example : Multiset.card (↑([1, 2, 3] : List Nat) : Multiset Nat) = 3 := by trivial              -- L01
example : (↑([1, 2, 3] : List Nat) : Multiset Nat) = ↑([3, 1, 2] : List Nat) := by trivial      -- L02
example : Multiset.card (Multiset.map (· + 10) ...) = 3 := by trivial                            -- L03
example : Multiset.count 1 (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = 2 := by trivial        -- L04
example : Multiset.toFinset (...) = {1, 2, 3} := by trivial                                      -- L05
example : ([1, 2, 3] : List Nat).toFinset = ([3, 2, 1, 2] : List Nat).toFinset := by trivial     -- L06
example : ... = 4 ∧ ... .card = 3 := by trivial                                                  -- L07
example : (Multiset.toFinset ...).val = Multiset.dedup ... := by trivial                          -- L08
example : m.card = 5 ∧ ... ∧ s.card = 3 ∧ s = {1, 2, 3} := by trivial                           -- L09 (boss)
```

A learner can complete the entire world by typing `trivial` nine times. They learn nothing.

**Fix**: Add `DisabledTactic trivial` to every level file. Based on the pattern established in W3_ex (FinThreeExamples), also disable `native_decide`, `simp`, `aesop`, and `simp_all`. For levels where `decide` is not the intended tactic, disable `decide` as well (see P0-2).

---

### P0-2: `decide` closes levels where it is NOT the intended tactic

**Severity**: P0 (blocking)
**Type**: Statement exploitability -- per-level
**Details**: `decide` is intended in L02 (after `rw`), L04, L05, L06, and parts of L07/L09. But it also closes:

| Level | Intended proof | `decide` alone closes it? | Bypass |
|-------|---------------|--------------------------|--------|
| L01 | `rfl` | YES | Bypasses learning that `card` on coerced list is *definitionally* equal to `length` |
| L03 | `rw [Multiset.card_map]; rfl` | YES | Bypasses learning `Multiset.card_map` entirely |
| L07 | `constructor` + subgoals | YES (one-shot) | Bypasses learning to split conjunctions with `constructor` |
| L08 | `exact Multiset.toFinset_val _` | YES | Bypasses learning `Multiset.toFinset_val` |
| L09 | `constructor` chain + `rfl`/`decide` | YES (one-shot) | Bypasses the entire boss integration |

**Fix**:
- L01: Disable `decide` (the intended proof is `rfl`; both are computation, but `rfl` teaches definitional equality)
- L03: Disable `decide` (the intended proof is `rw [Multiset.card_map]; rfl`; the learner must learn `card_map`)
- L07: Disable `decide` (the intended proof requires `constructor` first; one-shot `decide` bypasses the lesson)
- L08: Disable `decide` (the intended proof is `exact Multiset.toFinset_val _`; `decide` bypasses the lemma)
- L09: Disable `decide` (the boss should require `constructor` splitting, not one-shot computation)

Note: `rfl` also closes L08, which means `exact Multiset.toFinset_val _` is not forced even without `decide`. The statement is definitionally equal, so `rfl` works. This is a lesser issue (both are "exact proof" moves), but ideally the statement should require the learner to use the named lemma. Possible fix: make the statement generic or partially abstract.

---

### P0-3: `aesop` closes the boss (L09)

**Severity**: P0 (blocking)
**Type**: Statement exploitability
**Details**: `aesop` closes the entire boss in one shot. The boss should require the learner to integrate multiple proof moves manually.

**Fix**: Add `aesop` to the `DisabledTactic` line for L09.

---

### P0-4: Boss is a gauntlet, not an integration (failure taxonomy #8b)

**Severity**: P0 (blocking)
**Type**: Boss design
**Details**: The boss (L09) is a four-part conjunction where each part is independently closed by `rfl` or `decide`. The learner does `constructor; rfl; constructor; decide; constructor; decide; decide`. This is concatenation of independent computations, not integration. There is no moment where the learner must see the structure, plan ahead, combine moves from different levels, or make a non-obvious choice.

The plan says the boss should test "Integration of M16--M20, C3, C4," but the proof does not use `Multiset.coe_eq_coe`, `Multiset.card_map`, `Multiset.toFinset_val`, or any other lemma from the world. Every conjunct is closed by `decide` (or `rfl`), which was introduced in W2.

**Fix**: Redesign the boss to require at least one non-trivial proof step specific to W4:
- One conjunct should require `rw [Multiset.coe_eq_coe]` (integration of L02)
- One conjunct should require `rw [Multiset.card_map]` (integration of L03)
- One conjunct could require `exact Multiset.toFinset_val _` (integration of L08)
- The statement should use a different list than `[1, 2, 1, 3, 2]` and possibly involve `Multiset.map` or a permutation argument

Example boss skeleton:
```lean
-- Prove that mapping (+1) over the multiset from [0,1,0,2] gives
-- the same multiset as [1,2,1,3], and both have finset {1,2,3}
Statement :
    let m₁ : Multiset Nat := ↑([0, 1, 0, 2] : List Nat)
    let m₂ : Multiset Nat := Multiset.map (· + 1) m₁
    m₂ = ↑([1, 2, 1, 3] : List Nat) ∧ m₂.toFinset = {1, 2, 3} := by
  constructor
  · rw [Multiset.coe_eq_coe]  -- reduce to permutation
    decide                      -- verify permutation
  · decide                      -- verify finset equality
```

---

## P1 issues (high)

### P1-1: No new proof moves taught in the entire world

**Severity**: P1 (high)
**Type**: Coverage -- proof-move layer empty
**Details**: The world introduces 8 new definitions/theorems (`Multiset`, `Multiset.card`, `List.Perm`, `Multiset.coe_eq_coe`, `Multiset.map`, `Multiset.card_map`, `Multiset.count`, `Multiset.toFinset`, `List.toFinset`, `Multiset.dedup`, `Multiset.Nodup`, `Multiset.toFinset_val`) but uses only pre-existing tactics: `rfl`, `decide`, `constructor`, `rw`, `exact`. The learner acquires definitions but no new ways of reasoning.

**Fix**: Add levels that require symbolic reasoning:
- A level using `Multiset.count_cons_self` / `Multiset.count_cons_of_ne` (as enrichment suggestion #1)
- A level using `Multiset.mem_coe` (as enrichment suggestion #6)
- Consider a level using `Multiset.card_toFinset_le_card` (as enrichment suggestion #3)

### P1-2: `Multiset.mem` / `∈` for multisets is never introduced

**Severity**: P1 (high)
**Type**: Coverage gap
**Details**: Membership is the most fundamental operation on a collection type. The world introduces `Multiset.card`, `Multiset.count`, `Multiset.map`, and `Multiset.toFinset` but never introduces `∈` for multisets. The learner saw `List.mem` in W3 and will see `Finset.mem` in W6, but the middle layer of the hierarchy is missing.

**Fix**: Add a level introducing `Multiset.mem_coe : a ∈ (↑l : Multiset α) ↔ a ∈ l`.

### P1-3: No scaffold fade -- every level is equally easy

**Severity**: P1 (high)
**Type**: Granularity -- progression absent
**Details**: Every level has the same difficulty: one tactic (or at most two: `rw` + `decide`, `constructor` + `rfl`/`decide`). There is no worked example with heavy scaffolding, no practice with reduced scaffolding, no retrieval, no transfer. The entire world operates at the "first contact with minimal computation" level.

**Fix**: After the enrichment suggestions are implemented (symbolic reasoning levels, membership level, inequality level), the world should have a natural gradient: computational levels early, symbolic reasoning in the middle, integration at the boss.

---

## P2 issues (medium)

### P2-1: L08 intended proof (`exact Multiset.toFinset_val _`) is not forced -- `rfl` works

**Severity**: P2 (medium)
**Type**: Statement exploitability -- minor
**Details**: L08 intends the learner to use `exact Multiset.toFinset_val _`, but `rfl` closes the goal because the equality is definitional. The learner can bypass the named lemma.

**Fix**: Low priority after P0/P1 fixes. Options:
1. Accept `rfl` as a valid proof (it is still correct and teaches definitional equality)
2. Make the statement slightly non-definitional (e.g., use a variable `m` instead of a concrete list)

### P2-2: L07 has no `NewTheorem` or `NewDefinition` line

**Severity**: P2 (medium)
**Type**: Inventory gap
**Details**: L07 (ThreeLayers) is one of the most conceptually important levels but introduces no new inventory items. It implicitly uses `Finset.card` but does not declare `NewDefinition Finset.card`. The learner sees `s.toFinset.card` without `Finset.card` being formally documented.

**Fix**: Add `NewDefinition Finset.card` to L07.

### P2-3: Hints are too direct -- no strategy hints before answer hints

**Severity**: P2 (medium)
**Type**: Hint design
**Details**: Every hint immediately names the tactic to try. There are no strategy-level hints ("What type of proof is this? What does the goal look like?") before the answer hints. The operational lessons reference doc says hints should be layered: strategy first, then code.

Examples:
- L01 hint: "Try `rfl`." -- no strategy layer
- L04 hint: "Try `decide`." -- no strategy layer
- L09 hint: "Use `constructor`." -- no strategy layer

**Fix**: Add a strategy-level `Hint` before each direct-answer hint. Example for L01:
```
Hint "The goal is an equality between two natural numbers. Look at both sides -- are they definitionally equal? If so, what tactic proves definitional equalities?"
Hint "Try `rfl`."
```

### P2-4: No `Branch` hints for wrong moves

**Severity**: P2 (medium)
**Type**: Hint design -- recoverability
**Details**: None of the levels have `Branch` hints catching common wrong moves. For example:
- In L02, a learner might try `decide` directly (which now actually works as an exploit, but if it were disabled, they would be stuck)
- In L03, a learner might try `rfl` directly (which does not work before `rw [Multiset.card_map]`)
- In L08, a learner might try `rfl` instead of `exact Multiset.toFinset_val _`

**Fix**: Add `Branch` hints for common wrong approaches, at least for L02, L03, and L08.

### P2-5: L06 conclusion mentions non-injectivity but never connects to proof

**Severity**: P2 (medium)
**Type**: Transfer gap
**Details**: L06's conclusion says "This demonstrates that `toFinset` is not injective" but the learner never proves non-injectivity. They prove that two specific inputs give the same output (`decide`), but never prove the general statement or even articulate why this implies non-injectivity.

**Fix**: Low priority. Consider adding a sentence connecting the specific proof to the general concept.

---

## Learner simulation

### Attentive novice

**First stuck point**: Nowhere. Every level can be closed by `trivial` or `decide` (both available). The novice types `decide` or follows the hint (which says "Try `decide`") and passes every level.

**Most likely wrong move**: In L03, the novice might try `rfl` before `rw [Multiset.card_map]`. If `decide` is disabled, the hint path rescues. If `decide` is not disabled, the novice never encounters the stuck point.

**Hints rescue well?**: The hints are functional but not pedagogically rich. They give the answer immediately with no thinking time.

**Lesson legibility**: The learner exits the world knowing "multisets exist, they forget order but keep duplicates, and you can convert to finsets." They do NOT learn how to prove anything about multisets that cannot be resolved by `decide` on a concrete example. The gap will be felt in W4_ex and later worlds.

**Key risk**: The novice develops a false sense of fluency. They "completed 9 levels" but never wrote a proof that required thought. When W5 introduces finsets with non-trivial proof demands, the transition will feel abrupt.

### Experienced Lean user

**Avoidable friction**: Near zero -- in fact, too little friction. The experienced user types `decide` or `trivial` for every level and finishes the world in under 2 minutes. No level requires engagement.

**Alias gaps**: `native_decide` works in most places, which is fine. `norm_num` works on L01 and L03.

**Inventory clutter**: Acceptable -- 8 new definitions/theorems is within bounds for a 9-level world.

**Needless forced verbosity**: None. The proofs are all one-liners or short.

**Overall assessment**: An experienced user will view this world as entirely trivial and may develop contempt for the course's difficulty calibration.

---

## Boss integrity check (L09)

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | PARTIAL | `constructor` (W1), `rfl` (W1), `decide` (W2) are seeded. But no W4-specific subskill is tested. |
| Closure quality | FAIL | The boss uses no lemma or proof move introduced in W4. |
| Integration quality | FAIL | Gauntlet boss: four independent computations concatenated by `constructor`. No interaction between parts. |
| Surprise burden | NONE | No new difficulty at all. |
| Can learner explain proof? | YES but trivially | "I split the conjunction four times and computed each piece." No mathematical insight required. |

**Verdict**: The boss fails the integration test. It is a **gauntlet boss** (failure taxonomy #8b).

---

## Course-role sanity

**Intended role**: Lecture world
**Actual role**: Definition tour with computation exercises

A lecture world should teach proof moves alongside definitions. This world introduces many definitions but the "proof" in every level is mechanical computation (`rfl`, `decide`). It behaves more like a "glossary world" than a lecture world. The learner cannot generalize any technique from this world to a non-concrete setting.

**Fix**: The enrichment review's suggestions (adding symbolic reasoning levels) would correct this. After those additions, the world would genuinely function as a lecture world.

---

## Ranked patch list

| Priority | Issue | Fix | Files affected |
|----------|-------|-----|---------------|
| 1 | P0-1: `trivial` closes all 9 levels | Add `DisabledTactic trivial native_decide simp aesop simp_all` to ALL 9 level files | L01--L09 |
| 2 | P0-2: `decide` closes non-`decide` levels | Add `decide` to `DisabledTactic` for L01, L03, L07, L08, L09 | L01, L03, L07, L08, L09 |
| 3 | P0-3: `aesop` closes boss | Already covered by patch 1's `DisabledTactic` line | L09 |
| 4 | P0-4: Boss is a gauntlet | Redesign L09 statement to require at least one `rw [Multiset.coe_eq_coe]` or `rw [Multiset.card_map]` step | L09 |
| 5 | P1-1: No new proof moves | Implement enrichment suggestions #1, #2, #3, #6 (add symbolic-reasoning levels for `count`, `mem`, inequality, list-inequality) | New level files; renumber existing |
| 6 | P1-2: `Multiset.mem` missing | Add a level for `Multiset.mem_coe` (enrichment #6) | New level file |
| 7 | P1-3: No scaffold fade | After new levels are added, reorder to create difficulty gradient: computation -> symbolic -> integration | World file import order |
| 8 | P2-2: `Finset.card` undocumented | Add `NewDefinition Finset.card` to L07 | L07 |
| 9 | P2-3: Hints too direct | Add strategy-level hints before answer hints | L01--L09 |
| 10 | P2-4: No `Branch` hints | Add `Branch` hints for common wrong moves in L02, L03, L08 | L02, L03, L08 |
| 11 | P2-1: L08 exploitable by `rfl` | Consider making statement non-definitional (low priority) | L08 |
| 12 | P2-5: Non-injectivity not connected to proof | Add transfer sentence to L06 conclusion | L06 |

---

## What to playtest again after patching

1. **All 9 levels**: Re-test `trivial`, `decide`, `simp`, `aesop`, `native_decide`, `simp_all`, `norm_num` on every level after `DisabledTactic` lines are added. Confirm that the intended proof path is the only non-disabled path.

2. **New levels** (from enrichment): Full playtest of any new symbolic-reasoning levels (count_cons, mem_coe, inequality, list-inequality). These are first-contact levels and need careful hint/granularity checking.

3. **Boss (L09)**: After redesign, verify:
   - No one-shot exploit
   - Requires at least 3 distinct W4-specific proof moves
   - All subskills seeded in earlier levels
   - Hints cover all stuck points

4. **Level numbering**: After new levels are inserted, verify that `Level N` matches `L{NN}` file naming, and that the world file imports are in order.

5. **Build**: `lake build` after all patches.
