# W4_ex ListUnderLenses -- Playtest Audit Round 2

**World**: ListUnderLenses (6 levels, up from 5 in R1)
**Role**: Example world examining `[1,2,1,3]` under three lenses (list, multiset, finset)
**Predecessor**: MultisetHierarchy (W4)
**Changes since R1**: L01 adds membership, L02 adds `mem_coe`, L04 adds same-finset, new L05 (`card_map` with `decide` disabled), L06 boss expanded to 5-part conjunction.

---

## 1. Overall Verdict

**NEEDS REVISION.** The structural improvements from R1 are solid -- L05 is a good addition and the boss expansion to 5 parts is a real improvement. However, the core R1 finding (`decide` closes every level without engaging with the intended lessons) has only been partially addressed: `decide` is disabled on L05 only. L01, L02, L03, L04, and L06 (the boss) all remain one-shottable by `decide`. The R1 P1 finding about zero inventory declarations is also unaddressed. A new P1 exploit exists on L05 where `rfl` bypasses the `rw [Multiset.card_map]` lesson.

---

## 2. Rubric Scores

| Category | Score | R1 | Delta | Notes |
|----------|-------|-----|-------|-------|
| 1. Coverage closure | 2 | 2 | = | Bridge-lemma lessons remain unenforced on L01, L02, L04, L06 |
| 2. Granularity fit | 3 | 3 | = | L05 addition is appropriate; each level has one dominant lens |
| 3. Proof-move teaching | 2 | 2 | = | `decide` bypass still present on 5/6 levels |
| 4. Inventory design | 1 | 1 | = | Still zero NewTactic/NewTheorem/NewDefinition in entire world |
| 5. Hint design / recoverability | 3 | 3 | = | Hints are properly layered; L05 hints are well-structured |
| 6. Progression (worked example -> boss) | 3 | 2 | +1 | Boss expanded from 4 to 5 parts; part 4 (`toFinset_card_le`) and part 5 (`card_map`) require non-`decide` moves -- though the whole boss is still closable by `decide` since `decide` is not disabled |
| 7. Mathematical authenticity | 3 | 3 | = | Three-lenses narrative remains clear and well-motivated |
| 8. Paper-proof transfer | 3 | 3 | = | "In plain language" sections in every conclusion |
| 9. Technical fit | 2 | 2 | = | Compiles; `decide` exploit persists on 5/6 levels |

**Average: 2.4 -- still below the 3.0 threshold.**

---

## 3. Coverage Gaps

### 3a. `decide` closes L01, L02, L03, L04, L06 as one-shot (P0 -- PERSISTS FROM R1)

Verified by running Lean:

| Level | Intended proof | `decide` closes? | `norm_num` closes? |
|-------|---------------|-------------------|---------------------|
| L01 | `constructor; rfl; decide` | YES | YES |
| L02 | `constructor; rfl; rw [mem_coe]; decide` | YES | YES |
| L03 | `constructor; decide; decide` | YES | NO (finset equality blocks) |
| L04 | `constructor; rw [coe_eq_coe]; decide; decide` | YES | NO (perm blocks) |
| L05 | `rw [Multiset.card_map]` | NO (`decide` disabled) | NO (`norm_num` disabled) |
| L06 | `constructor` chain + mixed tactics | YES | NO (perm blocks) |

The R1 P0 finding was: "`decide` closes L02, L04, L05 entirely, bypassing bridge-lemma lessons." The fix applied was to disable `decide` only on L05. L02 and L04 (and the boss L06) remain exploitable.

**Critical on L06 (boss)**: The boss is the integration level. If `decide` closes the entire 5-part boss, the learner needs zero technique from any prior level. This undermines the entire world.

**Note on the fundamental tension**: R1 correctly identified that disabling `decide` on L02 and L04 breaks the intended proofs (which use `decide` as the compute step after a bridge-lemma rewrite). The resolution chosen was to accept the exploit on L01-L04 and disable on L05 only. This is defensible for the practice levels (L01-L04), but NOT for the boss (L06). The boss must disable `decide` to force integration.

**Recommendation**: Disable `decide` on L06. The boss proof already uses techniques that don't need `decide` for parts 1, 4, and 5 (`rfl`, `exact toFinset_card_le _`, `rw [Multiset.card_map]`). For parts 2 and 3, the boss proof uses `decide` after rewrites -- but with `decide` disabled, an alternative is needed. Options:
- Use `exact Quotient.sound (...)` or `List.Perm` constructors for part 2 (too advanced)
- Use `native_decide` (already disabled)
- **Best option**: Replace parts 2 and 3 in the boss with statements that do NOT require `decide`. For example, replace part 3 (finset card = 3) with a statement about membership (`2 ∈ toFinset ↑[1,2,1,3]`) that can be proved via `rw [Multiset.toFinset_coe]; rw [List.mem_toFinset]; decide`... but that still uses `decide`.

**Alternative best option**: Accept the tension. On the boss, disable `decide` and change parts 2 and 3 to theorems that can be proved without `decide`:
- Part 2: prove the multiset cardinality equals 4 using `rfl` (instead of proving two multisets are equal)
- Part 3: prove that the finset card + (multiset card - finset card) = multiset card using `omega` or `rfl`

Or accept as P2 and document: the example world inherently works with concrete data, and concrete data is decidable.

### 3b. `rfl` closes L05, bypassing `rw [Multiset.card_map]` (P1 -- NEW)

L05 disables `decide` and `norm_num` to force the learner to use `rw [Multiset.card_map]`. However, `rfl` closes L05 because `Multiset.card (Multiset.map f ↑l)` is definitionally equal to `Multiset.card ↑l` on concrete data (both reduce to `List.length l`).

`rfl` cannot be disabled. This is an inherent limitation.

**Severity**: P1 rather than P0 because the learner would need to discover that `rfl` works here (not obvious), and `rfl` at least demonstrates something mathematically correct (the equality is definitional). But it does bypass the bridge-lemma lesson.

**Recommendation**: Accept as P2. The intro text and hints guide toward `rw [Multiset.card_map]`, and `rfl` working here is not easily discoverable. Alternatively, restructure the statement to use symbolic data (variables) instead of concrete lists, but that changes the world's identity as an example world.

### 3c. `norm_num` closes L01 and L02 (P1 -- PERSISTS FROM R1)

`norm_num` is not disabled on L01 or L02, and closes both as one-shot. `norm_num` does NOT close L03, L04, or L06.

**Recommendation**: Add `norm_num` to `DisabledTactic` on L01 and L02. Low cost, no impact on intended proofs.

### 3d. Zero inventory declarations (P1 -- PERSISTS FROM R1)

The world has no `NewTheorem`, `NewDefinition`, or `NewTactic` declarations. The boss uses `Multiset.toFinset_card_le` and `Multiset.card_map` (both taught in W4), but these are not surfaced in the ListUnderLenses inventory panel. A learner who forgot these theorems has no in-panel reminder.

**Recommendation**: Add retrieval reminders for the key theorems used:
- L02: `NewTheorem Multiset.mem_coe` (retrieval from W4 L02)
- L04: `NewTheorem Multiset.coe_eq_coe` (retrieval from W4 L03)
- L05: `NewTheorem Multiset.card_map` (retrieval from W4 L05)
- L06: `NewTheorem Multiset.toFinset_card_le` (retrieval from W4 L11)

---

## 4. Granularity Defects

### 4a. Boss gauntlet concern -- IMPROVED but not fully resolved (P2, down from P1)

The boss expanded from 4 to 5 parts. The 5 parts are:

1. `list.length = multiset.card` -- `rfl`
2. multiset equality under reordering -- `rw [coe_eq_coe]; decide`
3. finset card = 3 -- `decide`
4. finset card <= multiset card -- `exact toFinset_card_le _`
5. map preserves card -- `rw [card_map]`

Part 4 requires applying a **general theorem** (`toFinset_card_le`) rather than computing on concrete data. Part 5 requires the `card_map` bridge lemma. These two parts add genuine integration variety beyond pure `decide` replay.

However, the 5 parts are still independent -- solving one does not help solve another. The boss is a playlist, not a composition. Each conjunct maps 1:1 to an earlier level. The learner's planning challenge is "remember which technique goes with which statement type" which is good retrieval practice but not integration in the strong sense.

**Verdict**: For an example world, this is acceptable. The world's purpose is to cement concrete understanding, not to teach novel proof composition. The boss conclusion's summary table is excellent as a study aid. Downgraded to P2.

### 4b. L01 and L03 are structurally very similar (P3 -- informational)

Both use `constructor; <computation>; <computation>`. The lenses differ (list vs finset) but the proof shape is identical. This is intentional parallel structure and helps the learner see what changes vs what stays the same. No fix needed.

---

## 5. Learner Simulation

### 5a. Attentive Novice

**L01 simulation**: Novice reads the introduction, learns about the three lenses. Sees `([1, 2, 1, 3] : List Nat).length = 4 ∧ (2 : Nat) ∈ [1, 2, 1, 3]`. Hint says "use `constructor`". After splitting: first goal is `length = 4`, hint suggests `rfl`. Second goal is `2 ∈ [1, 2, 1, 3]`, hint suggests `decide`. Clean experience.

**First likely stuck point**: L02, after `constructor` and `rfl` succeed for part 1. The novice sees `2 ∈ ↑[1, 2, 1, 3]` and tries `decide` -- which works, bypassing `mem_coe`. If the novice reads hints first (which an attentive novice would), they learn the reduce-then-compute pattern. **The hint rescue is good but the level does not enforce the lesson.**

**L04 simulation**: Novice sees multiset equality. Tries `rfl` (fails -- good). Reads hint, learns `Multiset.coe_eq_coe`. Uses `rw [Multiset.coe_eq_coe]; decide`. For part 2 (finset equality), tries `decide` -- works. Clean.

**L05 simulation**: `decide` is disabled. Novice reads hint about `Multiset.card_map`. Types `rw [Multiset.card_map]`. Goal closes. Might try `rfl` first (and succeed, bypassing the lesson). But the hint-first novice will follow the guided path.

**L06 simulation**: Novice sees a 5-part conjunction. Uses `constructor` to split. For each part, recalls the matching technique from the corresponding earlier level. Part 4 (`toFinset_card_le`) is the hardest retrieval -- the novice must remember a theorem from W4. Hint rescues well: "What general theorem states...?" with hidden hint giving the exact `exact` command.

**Most likely wrong move across the world**: Trying `decide` early and succeeding, then never learning the bridge lemma pattern. This is the core concern.

**Legibility of lessons**: Excellent when the learner follows hints. The narrative arc (list -> multiset -> finset -> permutation invariance -> map -> integration) is clear and well-paced. Each conclusion explains what was learned and connects to the next level.

### 5b. Experienced Lean User

**`decide` bypass**: An experienced user would immediately type `decide` on L01 and see it close the goal. They would then try `decide` on every subsequent level. Result: L02 `decide` (works), L03 `decide` (works), L04 `decide` (works), L05 `decide` (fails -- disabled), L06 `decide` (works). The experienced user learns nothing except that L05 blocks `decide`.

On L05, the experienced user would try `rfl` (works, bypassing the `card_map` lesson). On the boss, `decide` closes everything.

**Avoidable friction**: The type annotations `(↑([1, 2, 1, 3] : List Nat) : Multiset Nat)` are verbose. An experienced user would prefer shorter notation. This is acceptable -- Lean needs the annotations for correct type inference.

**Alias gap**: None significant. Bridge lemmas are properly named.

**Needless forced verbosity**: The repeated `constructor` calls in L06 are verbose but appropriate for a novice-targeted game. An experienced user could use `refine ⟨?_, ?_, ?_, ?_, ?_⟩` but that is not taught.

---

## 6. Boss Integrity Notes

### Boss (L06): Five-part integration

**Seeded subskills**:
1. `rfl` for definitional equality -- seeded in L01, L02
2. `rw [Multiset.coe_eq_coe]; decide` -- seeded in L04
3. `decide` for concrete computation -- seeded in L01, L03
4. `exact Multiset.toFinset_card_le _` -- taught in W4 L11
5. `rw [Multiset.card_map]` -- seeded in L05

All subskills are properly seeded. No surprise burdens.

**Closure quality**: Good. Each technique has introduction (in the corresponding level or W4) and at least one practice use.

**Integration quality**: Moderate. The five parts are independent -- no part depends on the result of another. The learner can solve them in any order. However, the variety of techniques (definitional equality, bridge lemma + decide, direct computation, general theorem application, bridge lemma with trivial finish) provides meaningful retrieval practice. For an example world, this level of integration is acceptable.

**Surprise burden**: Part 4 (`toFinset_card_le`) is from W4 L11, not from this world. This is the only cross-world retrieval. It is properly hinted.

**Could the learner explain in words why the proof works?** Yes. The conclusion's technique table maps each part to its proof move. The transfer section explains why finset cardinality differs from list length. A learner who solved the boss could articulate: "The list has 4 entries, the multiset has 4 items (same count, different structure), the finset has 3 elements (duplicates removed). Reordering doesn't change the multiset or finset. Mapping a function doesn't change the count."

---

## 7. Technical Risks

### 7a. `decide` on L06 boss (P0)

`decide` closes the entire 5-part boss as a one-shot. This is the most critical technical risk. The boss exists to force integration of techniques from L01-L05 and W4, but `decide` makes all of that unnecessary.

### 7b. `rfl` on L05 (P1)

`rfl` closes L05, bypassing `rw [Multiset.card_map]`. Cannot be fixed by disabling `rfl`. The level's pedagogical value depends on the learner following hints rather than trying `rfl`.

### 7c. No inventory declarations (P1)

Zero `NewTheorem` / `NewDefinition` / `NewTactic` in the entire world. The learner's inventory panel shows nothing new for this world. Key theorems used in L05 and L06 (`Multiset.card_map`, `Multiset.toFinset_card_le`) are not surfaced as retrieval reminders.

### 7d. `norm_num` on L01, L02 (P1)

`norm_num` closes L01 and L02 as one-shot. Not disabled. Low cost to fix.

### 7e. Build TacticDoc warnings (P3)

Cosmetic. Disabled tactics (`trivial`, `native_decide`, etc.) may trigger INFO-level warnings about missing TacticDocs. These are already defined in prior worlds and the game server should propagate them.

---

## 8. Ranked Patch List

| Priority | Issue | Fix |
|----------|-------|-----|
| **P0-1** | `decide` closes L06 boss as one-shot | Add `decide` to `DisabledTactic` on L06. Restructure the boss proof: replace parts 2 and 3 (which use `decide` in the intended proof) with `rw [Multiset.coe_eq_coe]; exact List.perm_of_... ` -- OR accept that parts 2 and 3 can't be proved without `decide` and instead change their statements to ones that don't need `decide`. **Simplest fix**: Replace boss part 2 (`multiset equality`) with `Multiset.card (↑[3,1,2,1]) = 4` (provable by `rfl`). Replace boss part 3 (`finset.card = 3`) with `([1,2,1,3] : List Nat).toFinset.card = 3` (provable by `rfl` if it reduces, otherwise `norm_num` -- test needed). If neither works, keep `decide` on L06 and accept as P2. |
| **P0-2** | `decide` closes L02 and L04, bypassing bridge-lemma lessons | Accept on L02 and L04 (the intended proofs use `decide` after the bridge rewrite, and there's no way to disable `decide` only before the rewrite). Document in the world design notes. The pedagogical mitigation is that hints guide the learner to the intended path. |
| **P1-1** | `rfl` closes L05, bypassing `rw [Multiset.card_map]` | Accept as inherent limitation. Cannot disable `rfl`. The hint-first path is pedagogically sound. |
| **P1-2** | `norm_num` closes L01 and L02 | Add `norm_num` to `DisabledTactic` on L01 and L02. |
| **P1-3** | Zero inventory declarations | Add `NewTheorem` lines: L02 should declare `Multiset.mem_coe`, L04 should declare `Multiset.coe_eq_coe`, L05 should declare `Multiset.card_map`, L06 should declare `Multiset.toFinset_card_le`. These are retrieval reminders (already taught in W4) but surface them in the inventory panel for this world. |
| **P2-1** | Boss is still somewhat gauntlet-like (5 independent parts) | Accept for an example world. The variety of proof techniques provides meaningful retrieval even without cross-part dependencies. |

---

## 9. What to Playtest Again After Patching

1. **P0-1**: After disabling `decide` on L06, verify the boss proof compiles with alternative approaches for parts 2 and 3. If the boss statement is changed, verify the new version compiles and the hints are correct.

2. **P1-2**: After adding `norm_num` to L01 and L02's `DisabledTactic`, verify both levels still build and the intended proofs work.

3. **P1-3**: After adding inventory declarations, verify `lake build` passes (no warnings about duplicate or conflicting declarations).

4. **Re-run full exploit check**: After all patches, run `decide`, `norm_num`, `rfl`, `omega`, and `trivial` against all 6 levels to verify no new exploits were introduced.

5. **Learner simulation on L06**: If the boss statement changes, re-simulate the novice path to ensure hints match the new proof structure.

---

## 10. R1 vs R2 Disposition

| R1 Issue | R1 Priority | R2 Status | Notes |
|----------|-------------|-----------|-------|
| `decide` closes L02, L04, L05 | P0 | **Partially fixed** | L05 fixed. L02, L04 remain. L06 boss added and also exploitable. |
| `decide` closes L01 without `constructor` | P0 | **Open** | Accepted as inherent to example world with concrete data |
| `norm_num` closes L01, L02 | P1 | **Open** | Not yet addressed |
| Boss is gauntlet | P1 | **Improved to P2** | 5-part boss with varied techniques is better than 4-part |
| No inventory declarations | P1 | **Open** | Still zero declarations |
| Plan/code misalignment L05 | P2 | **Resolved** | L05 is now `card_map`, L06 is boss. Plan alignment improved. |
| L01/L02 structural repetition | P2 | **Accepted** | Intentional parallel structure |
| TacticDoc warnings | P2 | **Accepted** | Cosmetic, handled by prior worlds |

---

## Summary

The R1-to-R2 improvements are structural improvements: adding L05 (`card_map` with `decide` disabled) and expanding the boss to 5 parts with more varied proof techniques. These are genuine improvements.

However, the core R1 finding -- `decide` closes most levels as one-shot -- is only partially addressed. The most critical remaining issue is that `decide` closes the **boss** (L06) as a one-shot, making the entire world's integration exercise trivially bypassable. The `norm_num` exploit on L01/L02 and the missing inventory declarations are also still open from R1.

**Minimum changes needed to pass R3**:
1. Disable `decide` on L06 (boss) -- may require changing the boss statement for parts that used `decide` in their intended proof.
2. Add `norm_num` to `DisabledTactic` on L01 and L02.
3. Add `NewTheorem` declarations for the bridge lemmas used in the world.
