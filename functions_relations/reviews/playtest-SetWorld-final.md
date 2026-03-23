# Playtest Review: SetWorld

**World**: SetWorld (9 levels)
**Role**: Onboarding + Lecture hybrid
**Course**: functions_relations

---

## 1. Overall Verdict: PASS

SetWorld is a well-constructed onboarding world. The central insight ("sets are predicates, membership is predicate evaluation") is clearly taught, progressively practiced, and integrated in the boss. All 9 levels have coherent dominant lessons, the boss integrates 5+ distinct moves, and the inventory is clean. No P0 defects found. Several P2 improvements are possible.

---

## 2. Rubric Scores

| Category | Score | Notes |
|---|---|---|
| Coverage closure | 3 | All planned items covered. `show` and `contradiction` thin on practice within this world (reinforced later). |
| Granularity fit | 4 | Each level has one dominant lesson. World center of gravity is stable throughout. Extra levels (L05, L08) fill genuine gaps vs plan. |
| Proof-move teaching | 4 | Proof shapes explicitly taught: `show` -> compute, `intro` -> contradiction, `use` witness, `obtain` -> destructure. Conclusions explain why, not just what. |
| Inventory design | 3 | Items unlocked at right times. Good docs. Minor: `change` undocumented, `dsimp` not disabled. |
| Hint design and recoverability | 3 | Layered hints throughout. L03 Branch catches direct-intro path. L09 Branch catches one-step obtain. Missing: L02 Branch for bare `omega`. |
| Worked example -> practice -> transfer -> boss | 3 | Clear progression from L01 demonstration through L03-L08 practice to L09 integration. Transfer deferred to PsetSets (correct for lecture world). |
| Mathematical authenticity | 4 | The set-predicate connection is the heart of the world and it's excellent. Even/odd, finite/infinite, compound predicates all concretize. Conclusion tables connecting sets to logic are very good. |
| Paper-proof transfer | 3 | Most conclusions connect Lean to informal reasoning. L05 comparison table is excellent. Some conclusions lean Lean-centric. |
| Technical fit and maintainability | 3 | Build succeeds. Dependencies clean. Minor: duplicate TheoremDoc for Set.mem_univ (L01 and L07). |

**Average**: 3.33
**Minimum**: 3

---

## 3. Summary Statistics

- 9 levels (plan specified 7; 2 added levels are valuable)
- 0 P0 defects
- 0 P1 defects
- 7 P2 defects
- No automatic red flags triggered

---

## 4. P0 Defects (blocking)

None.

---

## 5. P1 Defects (high priority)

None.

---

## 6. P2 Defects (medium)

**P2-1: `dsimp` not disabled — alternative to `show` in L02, L03**
`dsimp` can unfold set membership definitionally, enabling `dsimp; omega` to bypass the `show` lesson. A novice won't know `dsimp`, but an experienced user could skip the pedagogical point. Add `dsimp` to `DisabledTactic` in L02 and L03 (and possibly globally for this world).

**P2-2: `change` has no TacticDoc**
`change` is functionally identical to `show` for goal conversion. It's available to players but undocumented. If a learner discovers it (or knows it from elsewhere), they can't find documentation. Either add `TacticDoc «change»` to Metadata.lean or disable it in levels where `show` is the lesson.

**P2-3: L02 missing Branch for bare `omega`**
A novice's most likely wrong move in L02 is typing `omega` directly (without `show` first). `omega` probably fails on `3 ∈ {n | n < 5}` since it can't see through the set-membership wrapper, but the error message won't be helpful. A Branch catching this state with a hint saying "omega can't see through the set notation — use `show 3 < 5` first to make the arithmetic visible" would improve recoverability.

**P2-4: `show` under-practiced after L02-L03**
`show` is used in L02 and L03 (main path), then never again in SetWorld. The boss (L09) uses an abstract predicate where `show` is unnecessary. This is acceptable since `show` will be used heavily in later worlds (SubsetWorld, SetOpsWorld), but within this world the move gets only 2 uses.

**P2-5: `contradiction` introduced but under-used**
`contradiction` is introduced in L03 (via Branch) but never appears in the main path of any subsequent level. Its role as a rescue tactic (detecting contradictions through definitional wrappers) is valuable but gets minimal practice. Will be reinforced in later worlds.

**P2-6: Duplicate TheoremDoc for Set.mem_univ**
Both L01 (line 112) and L07 (line 48) declare `TheoremDoc Set.mem_univ as "Set.mem_univ" in "Set"`. Redundant. Remove the L07 copy.

**P2-7: L02 introduces two new burdens**
L02 teaches both set-builder notation (`{n | n < 5}`) and the `show` tactic. The novelty budget prefers one new burden per level. Mitigated by: the two are entangled (you need `show` specifically to work with set-builder notation), and the level's dominant lesson is their combination. Acceptable but noted.

---

## 7. Coverage Gaps

**Within SetWorld**: No critical coverage gaps. All planned theorem families are present.

**`show` closure**: Introduction (L02) + supported use (L03) only. No retrieval or integration within this world. Closure completes in later worlds.

**`obtain` closure**: Introduction (L05) + integration (L09 boss). No intermediate supported-use level. Thin but the boss provides the retrieval test.

**`contradiction` closure**: Introduction only (L03 Branch). No supported use. Very thin — but `contradiction` is a rescue tactic, not a primary proof move for this world.

---

## 8. Granularity Defects

None significant. The world has a clean progression:
- L01-L02: First contact with sets and `show`
- L03-L05: Non-membership patterns (simple arithmetic, then existential)
- L06-L07: Boundary sets (empty, universal)
- L08: Compound predicates (practice level bridging to boss)
- L09: Boss

L06 and L07 mirror each other (empty = False, univ = True) which could feel repetitive, but they serve distinct purposes: L06 teaches `exact h` on `False`, L07 reinforces `constructor` on `True` with `∀` quantification. Each carries its own dominant lesson.

---

## 9. Learner Simulation Notes

### Attentive novice

**First stuck point**: L05 — typing `obtain ⟨r, hr⟩ := h` with angle bracket notation. Hint covers this with `\<` and `\>` instructions. Recoverable.

**Second stuck point**: L09 part 2 — figuring out that `hq 3 h` produces `Even 3`. Hint says "Apply hq to 3 and h to derive that 3 must be even: `have h3 := hq 3 h`." This is a direct instruction. Recoverable.

**Most likely wrong move**: L02 — typing `omega` without `show`. Current hints don't cover this (see P2-3).

**Lesson legibility**: Excellent. Every introduction clearly states what the level teaches and why. Conclusions summarize and connect to prior levels. The L05 comparison table and L09 summary table are particularly good.

### Experienced Lean user

**Avoidable friction**: Low. `dsimp` works as an alternative to `show`. `exact True.intro` works instead of `constructor`. `exact fun n h => h` works for L06. These are all valid and don't cause errors.

**Alias gaps**: `change` undocumented (P2-2). `dsimp` available but unintroduced (P2-1). `norm_num` disabled (correct). `simp` disabled (correct).

**Inventory clutter**: Low — only 6 definitions, 3 new tactics, and 1 theorem tab through the whole world. Clean.

**Needless verbosity**: Introductions are detailed but justified for an onboarding world. An experienced user can skip the text and read the goal state directly.

---

## 10. Boss Integrity Notes

**Boss (L09)**: `4 ∈ {n | p n} ∧ 3 ∉ {n | p n}` with abstract predicate `p` and hypotheses `hp`, `hq`.

**Integrated moves** (5+):
1. `constructor` for ∧ — from L01, L08
2. `apply hp` — baseline (first real use on named hypothesis)
3. `use 2` for witness — from L04
4. `intro h` for negation — from L03
5. `have`/`obtain` for hypothesis chaining — from L05
6. `omega` for arithmetic — baseline

**Seeded subskills**: All boss moves appear in prior levels. ✓

**Surprise burden**: The `have h3 := hq 3 h` pattern (applying a function hypothesis to specific arguments) is the first explicit use of this form. Mitigated by: (a) the Branch catches the alternative `obtain ⟨r, hr⟩ := hq 3 h` one-step approach, (b) the hint gives the exact syntax, (c) `have` is baseline from NNG4.

**Can the learner explain the proof?** Yes: "4 is in the p-set because 4 is even and hp says every even number satisfies p. 3 is not in the p-set because if it were, hq would give Even 3, but 3 = r + r has no natural number solution." The proof structure maps directly to this reasoning. ✓

**Integration quality**: Not a gauntlet — the learner must plan: membership uses hp forward, non-membership uses hq backward. Different proof shapes are combined, not concatenated. ✓

**Abstract predicate design**: Excellent. Using abstract `p` instead of a concrete predicate forces the learner to use hypotheses rather than computing. This tests understanding of the predicate-evaluation concept, not just arithmetic. ✓

---

## 11. Technical Risks

- **`omega` preprocessing**: If `omega`'s internal preprocessing (which uses `simp`-like steps) can unfold set membership, it would one-shot L02 and others. The L03 Branch hint text ("omega cannot see through the set-membership wrapper directly") suggests the author tested this and `omega` does NOT unfold set membership. However, this should be verified on the actual game server, not just local build.

- **`setOf` display in goal state**: After `intro h` in L03, the hypothesis may display as `h : 7 ∈ setOf fun n => n < 5` rather than `h : 7 ∈ {n | n < 5}`. The L03 Branch hint text already uses the `setOf` form, suggesting the author observed this. Novices may find the `setOf` form confusing. Low risk since the introduction explains `setOf`.

- **Duplicate TheoremDoc**: Both L01 and L07 declare `TheoremDoc Set.mem_univ`. Lean accepted this (build succeeds), but it's unclear whether the game server handles duplicates gracefully. Remove the duplicate in L07.

---

## 12. Ranked Patch List

1. **Add `dsimp` to DisabledTactic** in all SetWorld levels (P2-1) — prevents experienced users from bypassing `show` lesson
2. **Add Branch to L02** for bare `omega` attempt with hint explaining why `show` is needed (P2-3) — catches novice's most likely wrong move
3. **Remove duplicate TheoremDoc** for `Set.mem_univ` from L07 (P2-6) — technical cleanup
4. **Add `TacticDoc «change»`** to Metadata.lean (P2-2) — documents an available tactic synonym
5. *Consider*: Add `unfold` and `delta` to DisabledTactic for completeness — these can also bypass `show`

---

## 13. What to Playtest Again After Patching

1. **L02 with `dsimp` disabled**: Verify that no other tactic can bypass the `show` lesson. Test: `omega`, `dsimp`, `unfold`, `change` (if disabled), `simp only []`.
2. **L02 Branch**: Verify the `omega` Branch fires correctly when the learner types `omega` on the set-membership goal.
3. **L09 boss**: Full walkthrough of both the main path and the Branch path to verify hint coherence after any changes.
4. **Goal state display**: Check what the player actually sees for `3 ∈ {n | n < 5}` — is it `{n | n < 5}` or `setOf fun n => n < 5`? Adjust hint text if needed.
