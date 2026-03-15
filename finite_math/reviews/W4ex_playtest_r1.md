# W4_ex ListUnderLenses -- Playtest Audit Round 1

**World**: ListUnderLenses (5 levels)
**Role**: Example world examining `[1,2,1,3]` under three lenses (list, multiset, finset)
**Predecessor**: MultisetHierarchy (W4, 14 levels)

---

## 1. Overall Verdict

**NEEDS REVISION.** The world compiles and the narrative is clear, but `decide` is not disabled on any level, which means a learner can bypass the intended bridge-lemma lessons (the entire pedagogical point of L02 and L04) with a single `decide`. The boss is a gauntlet (concatenation of earlier levels' proofs without novel integration). The plan/code alignment for L05 is off (plan says "Transfer", code says "Boss"). No inventory declarations exist in the entire world.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Bridge-lemma usage is the core lesson but `decide` bypasses it; no inventory to track what was taught |
| 2. Granularity fit | 3 | Each level has one dominant lens; L05 is a bit broad as 4-part conjunction but manageable |
| 3. Proof-move teaching | 2 | Intended proof moves are good, but unenforced -- `decide` closes everything |
| 4. Inventory design | 1 | Zero NewTactic/NewTheorem/NewDefinition in the entire world |
| 5. Hint design / recoverability | 3 | Hints are properly layered (strategy visible, code hidden); no dead-end coverage |
| 6. Progression (worked example -> boss) | 2 | Boss is a gauntlet (replay of L01-L04 in sequence, no novel integration) |
| 7. Mathematical authenticity | 3 | The three-lenses narrative is genuine and well-motivated |
| 8. Paper-proof transfer | 3 | "In plain language" sections in every conclusion are solid |
| 9. Technical fit | 2 | Compiles, but TacticDoc warnings; no inventory; decide exploit |

**Average: 2.3 -- below the 3.0 threshold for "good."**

---

## 3. Coverage Gaps

### 3a. `decide` exploit bypasses bridge-lemma lessons (P0)

| Level | Intended proof | Exploit |
|-------|---------------|---------|
| L01 | `constructor; rfl; decide` | `decide` (one shot) |
| L02 | `constructor; rfl; rw [mem_coe]; decide` | `decide` (one shot) |
| L03 | `constructor; decide; decide` | `decide` (one shot -- same tactic, just no `constructor`) |
| L04 | `rw [coe_eq_coe]; decide` | `decide` (one shot) |
| L05 | mixed: `rfl`, `rw [coe_eq_coe]; decide`, `decide`, `exact toFinset_card_le _` | `constructor <;> decide` (one shot) |

The core lesson of L02 is `rw [Multiset.mem_coe]` (reduce multiset membership to list membership). The core lesson of L04 is `rw [Multiset.coe_eq_coe]` (reduce multiset equality to permutation). If `decide` closes both goals directly, the learner never needs the bridge lemmas. This is the defining exploit of this world.

**L01 and L03**: `decide` is actually part of the intended proof (L01 part 2, L03 both parts). The issue is that `decide` also closes L01 part 1 (which should teach `rfl`) and closes L01/L03 without needing `constructor`. This is lower severity (P1) because the main lessons at those levels are "what does this representation look like" rather than a specific proof move.

**L02, L04, L05**: `decide` bypass is P0 because it defeats the intended lesson entirely.

### 3b. `norm_num` exploit (P1)

`norm_num` closes L01 and L02 entirely (same bypass as `decide`). It is not disabled. Lower severity than `decide` because `norm_num` is less obvious to reach for, but still an exploit.

### 3c. No inventory declarations (P1)

The world introduces no `NewTactic`, `NewTheorem`, `NewDefinition`, `TheoremDoc`, or `DefinitionDoc`. This is unusual for a world with 5 levels. Even an example world should acknowledge what the learner is practicing. At minimum, there should be `NewTheorem Multiset.toFinset_card_le` reminder (already introduced in W4 L11 but worth surfacing as a retrieval item).

More importantly, the boss uses `Multiset.toFinset_card_le` -- if the learner has forgotten it, there is nothing in the inventory panel to remind them.

### 3d. Plan/code misalignment for L05 (P2)

The plan (line 363) calls L05 "Transfer: State in plain English why |{1,2,3}| = 3 even though the list has 4 elements." The actual L05 is a four-part conjunction boss proof. The transfer moment exists in the boss conclusion text, but L05's role shifted from a dedicated transfer level to a boss level. The plan should be updated to reflect this, or a separate transfer level should be added.

---

## 4. Granularity Defects

### 4a. Boss is a gauntlet (P1)

L05 is labeled "Boss" but it is a concatenation of proof moves from L01-L04 with no novel integration challenge. The four conjuncts can be solved by replaying each earlier level's technique in sequence:
1. `rfl` (from L01/L02)
2. `rw [coe_eq_coe]; decide` (from L04)
3. `decide` (from L03)
4. `exact toFinset_card_le _` (from W4 L11)

There is no moment where the learner must see the whole structure rather than the pieces. Each conjunct is independent. The only new element is `Multiset.toFinset_card_le _` (part 4), which was taught in W4 L11 and is simply re-applied here.

**Recommendation**: Add a conjunct or restructure the boss so that one part depends on another part's result, forcing the learner to think about the hierarchy as a connected pipeline rather than four independent facts. For example: prove `list_length = multiset_card` and then use that to derive the finset inequality (combining `rfl` with `toFinset_card_le`). Or: add a part that requires `have` to name an intermediate result and use it in a subsequent step.

### 4b. L01 and L02 are structurally identical (P2)

Both L01 and L02 have the same shape: conjunction of (cardinality = 4) and (2 is a member). The proofs are nearly identical (`constructor; rfl; decide` vs `constructor; rfl; rw [mem_coe]; decide`). The structural similarity is intentional (parallel structure across lenses), but it does mean L02's distinctiveness rests entirely on the `rw [mem_coe]` step -- which, as noted above, `decide` bypasses.

---

## 5. Learner Simulation

### 5a. Attentive Novice

**First likely stuck point**: L02, after `constructor` and `rfl` succeed, the novice sees `2 ∈ ↑[1, 2, 1, 3]`. They might try `decide` (which works, bypassing the lesson). If they read the hint, they learn about `Multiset.mem_coe`. The hint rescue is good here -- but only triggers if the learner actually reads it before trying `decide`.

**Most likely wrong move**: Trying `rfl` on the membership goal in L02 (since `rfl` worked in L01 part 1 and L02 part 1). This will fail, and the learner will correctly seek a different approach. The hint handles this well.

**Legibility of lesson**: The L02 introduction clearly explains the reduce-then-compute pattern. The lesson is legible IF the learner follows the hints. But since `decide` works, the learner may never learn the bridge lemma.

**L04 simulation**: Novice sees `↑[1,2,1,3] = ↑[3,1,2,1]`. Might try `rfl` (fails). Might try `decide` (succeeds, bypassing lesson). Only if stuck and reading hints does the learner discover `coe_eq_coe`.

**L05 simulation**: Novice sees a 4-part conjunction. Knows `constructor` from L01-L04. Proceeds to split and solve each part using techniques from earlier levels. The `toFinset_card_le` part is the only retrieval challenge. The hint is good ("What general theorem states..."). If the learner remembers W4 L11, they apply it. If not, the hidden hint gives the exact `exact` command.

### 5b. Experienced Lean User

**Avoidable friction**: The type annotations `(↑([1, 2, 1, 3] : List Nat) : Multiset Nat)` are verbose but necessary for Lean to infer types correctly. An experienced user would find this noisy but understands why.

**`decide` bypass**: An experienced user would immediately see that `decide` closes every level and would type `decide` without engaging with any bridge lemma. The world teaches them nothing.

**`norm_num` bypass**: Similarly closes L01 and L02.

**Alias gap**: No significant alias gaps. The bridge lemmas are properly named.

**Needless forced verbosity**: None. Proofs are short and each step is one tactic.

---

## 6. Boss Integrity Notes

### Boss (L05): Gauntlet

**Seeded subskills**: All four proof moves appear in L01-L04 and W4 (toFinset_card_le). Seeding is complete.

**Closure quality**: Adequate -- each subskill has at least introduction and supported practice from predecessor levels.

**Integration quality**: POOR. The four conjuncts are independent. Solving conjunct 2 does not inform conjunct 3. There is no planning challenge: the learner splits the conjunction and applies the technique from the corresponding earlier level.

**Surprise burden**: Part 4 (`toFinset_card_le`) is a retrieval from W4 L11. This is the only non-trivial planning moment. It is properly hinted.

**Could the learner explain in words why the proof works?** Yes, because each step maps directly to one of the three lenses. The conclusion's summary table is excellent for this.

**Recommendation**: Either (a) accept that this is an example world where a gauntlet boss is acceptable because the purpose is reinforcement, not novel integration; or (b) add a step that requires combining results (e.g., use `have h := ...` then apply `h` in a later step).

---

## 7. Technical Risks

### 7a. Build warnings for TacticDoc (P2)

The build emits informational warnings about missing `TacticDoc` for `trivial`, `native_decide`, `simp`, `aesop`, `simp_all` in L05. These are INFO-level (not errors) and use existing docstrings. However, they should be resolved by adding `TacticDoc` entries in L01 (or earlier) of this world.

This is a systemic issue noted in MEMORY.md: "Always add TacticDoc for disabled tactics." Since these TacticDocs already exist in prior worlds (MultisetHierarchy L01), the warnings may be about ordering within the build. The game server should pick up the earlier definitions. These warnings are cosmetic but indicate the world is not self-contained.

### 7b. No `decide` disable creates drift from W4 (P1)

W4 (MultisetHierarchy) selectively disables `decide` on levels where it would bypass the lesson (L01, L05, L07, L10, L11, L13, L14). The example world W4_ex fails to carry this pattern forward. This is inconsistent.

---

## 8. Ranked Patch List

| Priority | Issue | Fix |
|----------|-------|-----|
| **P0-1** | `decide` closes L02, L04, L05 entirely, bypassing bridge-lemma lessons | Add `decide` to `DisabledTactic` on L02, L04, and L05. On L05, also disable `norm_num`. Keep `decide` available on L01 (part 2 needs it) and L03 (both parts need it). |
| **P0-2** | `decide` closes L01 without needing `constructor` | Either disable `decide` on L01 too (and replace the L01 membership proof with a manual approach), or accept that `decide` on L01 bypasses `constructor` + `rfl` (lower severity since the main lesson is the list perspective, not a proof technique). If keeping `decide`, at least the learner still sees the goal state. Recommendation: disable `decide` on L01 and use `List.Mem.head` or `List.Mem.tail` for the membership part, or restate the goal so `decide` is not needed. |
| **P0-3** | `norm_num` closes L01 and L02 entirely | Add `norm_num` to `DisabledTactic` on L01 and L02. |
| **P1-1** | L05 boss is a gauntlet -- no novel integration | Restructure boss to include at least one step that requires combining results. E.g., add a conjunct like "the number of elements lost by deduplication equals 1" (`multiset_card - finset_card = 1`), which requires the learner to combine cardinality computations rather than just replaying independent facts. Or use `have` to name an intermediate and use it later. |
| **P1-2** | No inventory declarations in the entire world | Add `NewTheorem Multiset.toFinset_card_le Multiset.mem_coe Multiset.coe_eq_coe` (as retrieval reminders) in appropriate levels. At minimum, surface `toFinset_card_le` before L05 where it is needed. |
| **P2-1** | Plan/code misalignment: plan says L05 is "Transfer", code says "Boss" | Update the plan to reflect the boss role, or add a separate L06 for the transfer question. The transfer moment is currently embedded in L05's conclusion text, which is adequate but not a standalone level. |
| **P2-2** | L01 and L02 structural repetition | Accept as intentional parallel structure. No fix needed unless L01 is restructured to avoid `decide` (see P0-2). |
| **P2-3** | Build TacticDoc warnings | Already covered by earlier worlds. Cosmetic. No action needed unless the game server does not propagate TacticDoc across worlds (in which case, add `TacticDoc trivial` etc. to L01). |

---

## 9. What to Playtest Again After Patching

After implementing the P0 and P1 fixes:

1. **Re-verify all 5 levels build** (`lake build`).
2. **Re-check L02 and L04 without `decide`**: Ensure the intended proof (`rw [mem_coe]; decide` for L02, `rw [coe_eq_coe]; decide` for L04) still works. Note: if `decide` is disabled, the learner needs another tactic for the second step. Check what other tactics can close the decidable subgoal after the bridge rewrite. Options: keep `decide` disabled only at the top level (before the rewrite), or find an alternative. Actually, the intended proof uses `decide` AFTER the rewrite -- so disabling `decide` globally breaks the intended proof too.

**This is the fundamental tension**: the intended proof pattern is `rw [bridge_lemma]; decide`. If `decide` is disabled, the learner cannot complete the intended proof. If `decide` is enabled, the learner can skip the bridge lemma entirely.

**Possible resolutions**:
- **(a)** Restructure the statements so `decide` does not close the unrewritten goal. E.g., for L02 membership, make the multiset non-concrete enough that `decide` fails before `rw [mem_coe]` but succeeds after. This is hard because both sides are concrete.
- **(b)** Accept the `decide` bypass on L01-L04 (these are rehearsal/practice levels in an example world, not first-contact levels) but disable `decide` on L05 (boss). For L05, the boss uses `decide` internally, so this requires restructuring the boss to avoid `decide`. Part 4 (`toFinset_card_le`) does not use `decide`, but parts 2 and 3 do.
- **(c)** Use `DisabledTheorem` to block specific decision procedures that `decide` invokes, rather than blocking `decide` itself. This is fragile and not recommended.
- **(d)** Accept the exploit as P2 (inherent limitation of concrete example worlds). Document it. Focus energy on ensuring the boss requires at least one non-`decide` move. Currently part 4 (`exact toFinset_card_le _`) is not closable by `decide` when the full conjunction is present... wait, I showed earlier that `constructor <;> decide` closes the whole boss. So even part 4 is closable by `decide`.

Let me verify: is part 4 individually closable by `decide`? Yes, I confirmed this above. So `decide` closes everything.

**Revised recommendation**: Accept that an example world working with fully concrete data inherently has `decide` as an available shortcut. The pedagogical mitigation is:
- Disable `decide` on L02, L04, and L05.
- On L02 and L04, replace the `decide` step in the intended proof with `exact List.Mem.tail _ (List.Mem.head _)` (L02) or `exact List.Perm.cons _ (List.Perm.swap _ _ _)` etc. -- but these are terrible for pedagogy.
- Better: disable `decide` on L05 only (the boss), and restructure the boss to not use `decide` at all. Accept `decide` bypass on L01-L04 as inherent to the example format.
- For L05 without `decide`: part 1 uses `rfl`, part 4 uses `exact toFinset_card_le _`. Parts 2 and 3 need restructuring. Part 2 (multiset equality) could use `rfl` if the lists are in the same order... but they are not. Part 3 (finset card) could use `rfl` if the expression reduces... let me check.

3. **Verify boss restructuring options**: Test whether the boss can work with `decide` disabled. If not, the boss statement may need to change.

4. **Re-run playtest audit (R2)** on the patched world.

---

## Summary

The ListUnderLenses world has a clear and well-motivated narrative, good hint layering, and solid transfer moments. However, it has one blocking issue: `decide` closes every level without engaging with the intended bridge-lemma lessons. The boss is a gauntlet without novel integration. No inventory declarations exist. These issues must be resolved before the world is complete.

The `decide` bypass is an inherent tension in example worlds that work with fully concrete data. The recommended resolution is to disable `decide` on levels where it bypasses a taught proof move (L02, L04, L05), while accepting that L01 and L03 legitimately use `decide` as part of their intended proofs. The boss (L05) needs the most attention: either restructure it to avoid `decide` entirely, or accept the exploit on a per-conjunct basis while ensuring at least one conjunct requires a non-trivial proof move.
