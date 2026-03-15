# W7 FinsetOperations -- Playtest Audit (Round 2)

**Auditor**: playtest-auditor (R2, fresh context)
**World**: FinsetOperations (10 levels: L01-L10)
**Changes since R1**: `NewTactic tauto` + `TacticDoc tauto` added to L09. Build passes.

---

## 1. Overall verdict

**CONDITIONAL PASS -- three P1 issues remain; no P0.**

The `tauto` declaration fix resolves the R1 finding. DisabledTactic lines are present on all 10 levels with the standard set (`trivial decide native_decide aesop simp_all`). No P0 blocking defects found. However, three P1 issues require attention: (a) library-lemma one-liners bypass the intended lesson on 5 of 10 levels, (b) `tauto` is declared but never used or demonstrated, creating dead inventory, and (c) the L08 introduction contains visible author self-revision text. One P2 issue: `norm_num` closes all concrete-finset levels (L01-L04) and is not disabled.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Operations well covered; `tauto` declared but not exercised; no misconception/counterexample level |
| Granularity fit | 3 | Each level has one dominant lesson; L05/L06 are structurally identical but defensible as consolidation |
| Proof-move teaching | 3 | Manual `ext` + membership-chase pattern taught clearly; negation reasoning in L10 underexplained |
| Inventory design | 2 | `tauto` is dead inventory; `Finset.subset_iff` and `Finset.ext_iff` referenced but undeclared |
| Hint design and recoverability | 3 | Thorough layered hints throughout; hidden hints at every decision point |
| Worked example -> practice -> transfer -> boss | 3 | Clean progression L01-L04 (intro) -> L05-L06 (ext) -> L07-L08 (practice) -> L09 (coached integration) -> L10 (boss) |
| Mathematical authenticity | 3 | Good transfer-to-paper-proof paragraphs; L03 summary table is strong; no counterexample level |
| Paper-proof transfer | 4 | L10 conclusion has a full paper-proof translation; every conclusion connects Lean to math |
| Technical fit and maintainability | 3 | Compiles clean; standard DisabledTactic on all levels; library-lemma exploits not gated |

**Average: 3.0 (meets threshold). One category below 3 (Inventory design = 2).**

---

## 3. Coverage gaps

### 3a. `tauto` -- declared but uncovered (P1)

`tauto` is introduced as `NewTactic` in L09 with a `TacticDoc`. But:
- L09's proof never uses `tauto`.
- L10's proof never uses `tauto`.
- No hint in either level demonstrates `tauto`.
- The `TacticDoc` says "after `simp` has reduced a membership goal to a proposition involving `and`, `or`, `not`, and `iff`, `tauto` can often finish the proof" -- but the learner never sees this happen.

This is a dead inventory item. The learner receives a tactic they have no idea how to use. The fix requires either (a) adding an alternative hint/proof path showing `ext a; simp [Finset.mem_union, Finset.mem_inter]; tauto` in L09 and/or L10, or (b) removing `NewTactic tauto` from this world and deferring to a later world.

**Coverage state**: I only. No S, R, G, or T.

### 3b. No misconception/counterexample level

The world proves seven positive set-algebraic facts and zero negative ones. The learner never encounters a false generalization. The most natural candidate: set difference is not symmetric (`{1,2,3} \ {2,3} != {2,3} \ {1,2,3}`). This was flagged by enrichment R1 (suggestion 2) but has not been implemented.

**Impact**: P2. The world is correct without it, but mathematical maturity requires encountering falsehoods.

### 3c. `Finset.subset_iff` referenced but undeclared

L07 introduces the subset proof pattern and mentions `Finset.subset_iff` in the introduction. No `NewTheorem` or `TheoremDoc` is declared. A learner who wants to `rw [Finset.subset_iff]` in a later world won't find it in their inventory.

**Impact**: P2. Inventory chain is broken for a lemma referenced by name.

### 3d. `Finset.ext_iff` referenced but undeclared

L05 introduces `Finset.ext_iff` in the introduction code block. No `NewTheorem` or `TheoremDoc` is declared. Only the `ext` tactic is declared.

**Impact**: P2. Same as above -- referenced theorem not in inventory.

---

## 4. Granularity defects

### 4a. L05 and L06 are structurally identical

Both prove commutativity via `ext` with identical proof skeletons. L06's introduction acknowledges this ("let's practice the `ext` proof pattern on a different operation"). L06 does introduce angle-bracket syntax (`rcases h with <hs, ht>`, `exact <ht, hs>`) for conjunctions, which is genuinely new. Verdict: acceptable as consolidation, but the L06 conclusion could do more to highlight what's new (the conjunction destructuring) versus what's repeated (the `ext` skeleton).

**Impact**: Not a defect -- noted for potential enrichment.

### 4b. L08 introduction is unfocused

The introduction contains author self-revision: "Actually, for this level you do NOT need `by_cases` -- this is a warm-up. But the next level will use it. Wait -- let's make this level actually use `by_cases`. Here is a better task:" This was flagged by enrichment R1 (suggestion 3) and R2 (suggestion 4) but remains unfixed.

**Impact**: P1 (polish). The learner will be confused by the visible decision-making process.

---

## 5. Statement exploitability

### Level-by-level exploit analysis

| Level | Statement | Exploitable? | Path | Severity | Disabled? |
|-------|-----------|-------------|------|----------|-----------|
| L01 | `2 in {1,2,3} cup {3,4,5}` | Yes | `simp` | P2 | No (`simp` intentionally available) |
| L01 | Same | Yes | `norm_num` | P2 | No |
| L02 | `3 in {1,2,3} cap {2,3,4}` | Yes | `simp` | P2 | No |
| L02 | Same | Yes | `norm_num` | P2 | No |
| L03 | `1 in {1,2,3} \ {2,3,4}` | Yes | `simp` | P2 | No |
| L03 | Same | Yes | `norm_num` | P2 | No |
| L04 | `3 in ({1,2,3} cup {3,4,5}) cap {2,3}` | Yes | `simp` | P2 | No |
| L04 | Same | Yes | `norm_num` | P2 | No |
| L05 | `s cup t = t cup s` | Yes | `exact Finset.union_comm s t` | P1 | No |
| L06 | `s cap t = t cap s` | Yes | `exact Finset.inter_comm s t` | P1 | No |
| L07 | `s subseteq s cup t` | Yes | `exact Finset.subset_union_left` | P1 | No |
| L07 | Same | Yes | `simp` | P2 | No |
| L08 | `s subseteq (s \ t) cup t` | No direct library one-liner | `intro a ha; simp [ha]` after intro | P2 | No |
| L09 | `s cap (t cup u) = (s cap t) cup (s cap u)` | Yes | `exact Finset.inter_union_distrib_left s t u` | P1 | No |
| L09 | Same | Yes | `ext a; simp [mem_union, mem_inter]; tauto` | P2 | No (`tauto` is available) |
| L10 | `s \ (t cap u) = (s \ t) cup (s \ u)` | Yes | `exact sdiff_inf` | P1 | No |
| L10 | Same | Yes | `ext a; simp [mem_sdiff, mem_inter, mem_union]; tauto` | P2 | No |

### P1 library-lemma exploits (5 levels affected)

The following library lemmas close the goal in one `exact` call, bypassing the intended `ext` + membership-chase proof entirely:

- **L05**: `Finset.union_comm s t`
- **L06**: `Finset.inter_comm s t`
- **L07**: `Finset.subset_union_left`
- **L09**: `Finset.inter_union_distrib_left s t u`
- **L10**: `sdiff_inf` (from the lattice algebra)

For L05-L06, L09, and L10, the entire point of the level is to prove the result via `ext`. A learner who uses `exact <library_lemma>` learns nothing about extensionality proofs. For L07, the point is the `intro a ha` subset proof pattern.

**Recommendation**: Add `DisabledTheorem` for these lemmas on the affected levels. Specifically:
- L05: `DisabledTheorem Finset.union_comm Finset.Union.comm`
- L06: `DisabledTheorem Finset.inter_comm Finset.Inter.comm`
- L07: `DisabledTheorem Finset.subset_union_left`
- L09: `DisabledTheorem Finset.inter_union_distrib_left`
- L10: `DisabledTheorem sdiff_inf`

Note: There may be additional lemma names (e.g., lattice-level versions like `sup_comm`, `inf_comm`, `inf_sup_left`). These should be tested and disabled as well.

### P2 `simp`/`norm_num` exploits (L01-L04)

Bare `simp` and `norm_num` both close all four concrete membership goals. Since `simp` is an intentionally available tactic (taught in W6), and these levels use `simp` as their final step anyway, the exploit is that `simp` can be applied at the start rather than after the rewriting steps. This is a pedagogical weakness but not a blocking issue: the hints guide the learner through the rewriting steps, and a learner who types `simp` has still "solved" the level correctly.

`norm_num` is not intentionally taught and could be disabled per-level. However, the project memory notes `norm_num` on membership as a known P2.

**Recommendation**: Accept `simp` exploits on L01-L04 as P2 (simp is a taught tool). Consider disabling `norm_num` on L01-L04 by adding `norm_num` to the DisabledTactic list.

### P2 `ext + simp + tauto` shortcut (L09, L10)

After `ext a`, `simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto` closes both L09 and L10. Since all three tactics (`ext`, `simp`, `tauto`) are available, this is a legal shortcut. It actually demonstrates what the world claims to teach: "ext + simp is the idiomatic pattern." If the world made this shortcut visible (via hints), it would be a feature rather than a bug.

**Recommendation**: Accept as P2. Better: make this the alternative proof path shown in hints (which also fixes the "tauto is dead inventory" issue).

---

## 6. Interactive proof quality

### All levels: generally good interactive flow

Each level's proof is a sequence of short tactic steps (`rw`, `rcases`, `constructor`, `left`/`right`, `exact`, `intro`), each producing a visible change in the goal state. No elaborate one-liners are required. The longest single step is `exact <hs, ht>` (angle bracket pair), which is short enough.

### L09 and L10: long but not hostile

L09 has approximately 25 tactic steps. L10 has approximately 30 tactic steps. Both are long but each step is individually simple. The hint coverage is thorough enough that a stuck learner can always get unstuck. The proof structure is visible in the hint tree.

### L10: negation reasoning requires implicit knowledge

In L10's forward direction (case `ht : a in t`), the learner must prove `a not in u` by writing `intro hu; apply hntu; rw [Finset.mem_inter]; exact <ht, hu>`. This is the first time in the world the learner constructs a proof of a negative statement by assuming the positive and deriving a contradiction. The hints explain this, but the move is genuinely new (not previously isolated). The conclusion mentions it as "negation reasoning" but does not give the pattern a name or a reusable formulation.

**Impact**: P2. The boss uses a proof move (intro-to-contradict for negation) that was never isolated in a standalone level. The hints rescue adequately, so it's not P1.

---

## 7. Learner simulation

### Attentive novice

**First likely stuck point**: L05, after `ext a`. The novice has never seen `ext` before and must now handle a biconditional goal. The transition from concrete finsets (L01-L04) to abstract finsets (L05) is abrupt. The novice may not know that `constructor` works on `iff` goals.

**Most likely wrong move**: In L05, trying `rw [Finset.mem_union]` before `constructor`, or trying to `apply` something to the `iff` goal. The hint at this point says "split the biconditional with `constructor`" which should rescue.

**Hint rescue quality**: Good. Hints are layered (open strategy hint, then hidden code hint) at every decision point. The novice can always recover.

**Lesson legibility**: Clear for L01-L04 (one new lemma each). Clear for L05 (ext is the new thing). L06 may feel like repetition -- the new skill (angle brackets for conjunction) is somewhat buried. L08's new skill (by_cases) is clear. L09-L10 are integration, and the novice will understand they are combining prior tools.

**L10 stuck point for novice**: The negation reasoning in the forward direction (case `a in t`). The novice must realize that to prove `a not in u`, they should assume `a in u` and derive a contradiction. The hint says "if `a` were in `u`, then `a in t cap u`, contradicting `hntu`," which gives the strategy. The hidden hint gives the exact code. Rescue is adequate.

### Experienced Lean user

**Avoidable friction**: The experienced user will immediately reach for `exact Finset.union_comm s t` on L05, `exact Finset.inter_comm s t` on L06, etc. These library lemmas are not disabled, so the experienced user can bypass every `ext` proof instantly. This is frustrating if the user wants to learn `ext`, and wasteful if they already know it.

**Alias gaps**: No alias issues found. `rw`/`simp`/`rcases`/`constructor`/`exact` are all standard.

**Inventory clutter**: `tauto` is introduced but never used, which adds clutter without value for the experienced user. The experienced user may try `tauto` after `ext a` and find it doesn't close the goal (because it needs `simp` first to reduce membership to propositions). Without a demonstration, the experienced user can't figure out `tauto`'s role.

**Needless forced verbosity**: L09 and L10 require 25-30 tactic steps when `ext a; simp [...]; tauto` would do it in 3. The experienced user would find this tedious. However, the pedagogical intent is clear (teach the manual proof), and the experienced user can use the shorter proof if they discover it.

---

## 8. Boss integrity (L10)

### Seeded subskills

| Subskill | Where seeded | Closure quality |
|----------|-------------|----------------|
| `ext` for finset equality | L05 (I), L06 (S), L09 (R) | Good |
| `mem_union` | L01 (I), L04 (S), L05 (R) | Good |
| `mem_inter` | L02 (I), L04 (S), L06 (R) | Good |
| `mem_sdiff` | L03 (I), L08 (S) | Adequate (only used once before boss) |
| `by_cases` on membership | L08 (I) | Minimal (one prior use) |
| `rcases` conjunction destruction | L06 (I) | Good |
| `rcases` disjunction destruction | L05 (I), L09 (S) | Good |
| Negation reasoning (intro + apply for contradiction) | **Not isolated** | **Gap** -- first appears in boss |

### Closure quality: adequate with one gap

`mem_sdiff` gets only one prior use (L08) after introduction (L03). `by_cases` gets only one prior use (L08) before the boss. This is thin but acceptable since both are simple tactics.

The negation reasoning pattern (proving `a not in X` by `intro; apply; ...`) appears for the first time in the boss. This is not isolated in any prior level. The hints are thorough enough to rescue, but it violates the "boss integrates, never introduces" principle.

**Impact**: P2. The hints rescue the learner, and the negation pattern is a straightforward extension of proof-by-contradiction, which the learner may know from NNG4. But ideally a level before the boss would isolate this pattern.

### Integration quality: strong

The boss requires combining `ext`, `mem_sdiff`, `mem_inter`, `mem_union`, `by_cases`, `rcases`, and negation reasoning. The forward direction has a genuine planning challenge (which side of the union gets `a`? depends on `by_cases` on `a in t`). The reverse direction requires case analysis on the union and then extracting pieces from the set difference. This is genuine integration, not mere concatenation.

### Surprise burden: acceptable

The proof is approximately 30 tactic steps, which is longer than anything in L01-L09 (L09 is the longest at approximately 25 steps). The increase is modest and the individual steps are all familiar (except the negation reasoning noted above).

### Can the learner explain why the proof works?

Yes. The conclusion provides a complete paper-proof translation. The proof structure mirrors the standard mathematical argument for De Morgan's law.

---

## 9. Course-role sanity

| Level | Intended role | Actual role | Verdict |
|-------|-------------|-------------|---------|
| L01 | First contact (mem_union) | First contact | Correct |
| L02 | First contact (mem_inter) | First contact | Correct |
| L03 | First contact (mem_sdiff) | First contact + summary | Correct |
| L04 | Supported practice (combining operations) | Supported practice | Correct |
| L05 | First contact (ext) | First contact | Correct |
| L06 | Practice (ext on intersection) | Consolidation + angle-bracket intro | Correct |
| L07 | First contact (subset proof pattern) | First contact | Correct |
| L08 | First contact (by_cases) | First contact | Correct |
| L09 | Coached integration (distributivity) | Coached integration | Correct |
| L10 | Boss (De Morgan) | Boss | Correct |

All levels play their intended roles. The progression from first-contact through practice to integration to boss is clean.

---

## 10. Technical risks

### 10a. Build status

Build passes (`lake build` verified by parent agent).

### 10b. DisabledTactic coverage

All 10 levels have: `DisabledTactic trivial decide native_decide aesop simp_all`. This is the standard set. Verified.

### 10c. `tauto` declaration

`NewTactic tauto` and `TacticDoc tauto` are present in L09. This resolves the prior missing-declaration issue. However, as noted, `tauto` is dead inventory (never used/demonstrated).

### 10d. Missing theorem docs

- `Finset.subset_iff` -- referenced in L07 introduction, no `TheoremDoc` or `NewTheorem`.
- `Finset.ext_iff` -- referenced in L05 introduction, no `TheoremDoc` or `NewTheorem`.

### 10e. `norm_num` not disabled

`norm_num` closes L01-L04 in one shot. It is not in the DisabledTactic list. Per project memory, this is a known P2 for concrete finset goals.

---

## 11. Ranked patch list

### P1 (High -- should fix before next round)

1. **Disable library-lemma exploits on L05, L06, L07, L09, L10.** Add `DisabledTheorem` for `Finset.union_comm`, `Finset.inter_comm`, `Finset.subset_union_left`, `Finset.inter_union_distrib_left`, and `sdiff_inf` (plus lattice-level aliases like `sup_comm`, `inf_comm`, `inf_sup_left`). Test to confirm no other lemma names bypass the goals. Without this, the intended proof (ext + membership chase) is completely bypassable on 5 of 10 levels.

2. **Fix `tauto` dead inventory.** Either (a) add alternative hints in L09 and/or L10 showing `ext a; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto` as a shortcut, with explanation of what `tauto` does, or (b) remove `NewTactic tauto` from L09 and defer to a later world. Option (a) is preferred because it also addresses the enrichment finding that the `ext + simp` pattern is promised but never demonstrated.

3. **Clean up L08 introduction.** Remove the visible self-revision ("Actually, for this level you do NOT need `by_cases`... Wait -- let's make this level actually use `by_cases`."). Present the `s subseteq (s \ t) cup t` task directly.

### P2 (Medium -- should fix, not blocking)

4. **Add `norm_num` to DisabledTactic on L01-L04.** Change the DisabledTactic line on these levels to `trivial decide native_decide aesop simp_all norm_num`. This prevents one-shot `norm_num` on concrete membership goals.

5. **Declare `Finset.subset_iff` as `NewTheorem` in L07.** Add `NewTheorem Finset.subset_iff` and a `TheoremDoc` to ensure the learner's inventory reflects the theorem they just learned to use.

6. **Declare `Finset.ext_iff` as `NewTheorem` in L05.** Add `NewTheorem Finset.ext_iff` and a `TheoremDoc` alongside the existing `ext` tactic declaration.

7. **Name the negation-reasoning pattern in L10.** Add a sentence to L10's introduction or a hint at the `intro hu; apply hntu` step: "To prove `a not in X`, introduce the assumption `a in X` and derive a contradiction. This is the standard pattern for proving negative statements."

### P3 (Low -- optional polish)

8. Name the "membership chase" proof pattern in L04 or L06 conclusion.

9. Add foreshadowing sentences to L01 and L02 conclusions pointing toward the L03 summary table.

10. Consider adding `omega` to DisabledTactic as a precaution (not currently exploitable, but future-proofing).

---

## 12. What to playtest again after patching

- **L05, L06, L07, L09, L10**: Verify that `DisabledTheorem` correctly blocks the library-lemma exploits. Test that the disabled theorem names are correct and complete (some lattice-level aliases may need to be added).
- **L09**: If `tauto` is given an alternative hint path, verify the hint fires at the right point and the `ext; simp; tauto` proof actually closes the goal within the game's proof state.
- **L08**: Verify the cleaned-up introduction reads coherently.
- **L01-L04**: If `norm_num` is disabled, verify levels still compile and the intended `simp` proof path still works.
