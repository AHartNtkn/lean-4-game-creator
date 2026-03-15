# W7 FinsetOperations -- Playtest Audit (Round 1)

**Auditor**: playtest-auditor (R1)
**World**: FinsetOperations (10 levels: L01--L10)
**Role**: Lecture world teaching union/inter/sdiff membership, `ext`, subset, `by_cases`
**Build**: Compiles successfully (lake build passes)

---

## 1. Overall verdict

**NOT PASSING.** Multiple P0 exploits remain open. Bare `simp` one-shots 6 of 10 levels (L01--L04, L07, L08). Library lemmas one-shot L05, L06, L07, L09. `norm_num` one-shots L01--L04. The boss (L10) can be closed in 2 tactic steps via `ext a; simp [...]; tauto` after `tauto` is introduced in L09. L08 still contains author's draft monologue ("Wait -- let's make this level actually use `by_cases`"). These issues must be resolved before the world can pass review.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Core items tracked, but `tauto` introduced without usage is a dead inventory item |
| 2. Granularity fit | 3 | Each level has one dominant lesson; L05/L06 are structurally near-identical but defensible as consolidation |
| 3. Proof-move teaching | 3 | The `ext` proof shape is taught clearly; membership-chase pattern is articulated in L04/L06 |
| 4. Inventory design | 2 | Missing `NewTheorem` for `Finset.subset_iff` (L07), `Finset.ext_iff` (L05); `tauto` introduced but never used; no `DisabledTheorem` for library lemma exploits |
| 5. Hint design / recoverability | 2 | L05/L06 reverse directions drop to zero intermediate hints; L08 contains draft text |
| 6. Worked example -> boss | 3 | Good progression L01-L04 -> L05-L06 -> L07-L08 -> L09 -> L10 boss |
| 7. Mathematical authenticity | 3 | Good transfer paragraphs, De Morgan's law proof is authentic |
| 8. Paper-proof transfer | 4 | L10 conclusion has full paper proof; every level has "In plain language" sections |
| 9. Technical fit / maintainability | 2 | P0 exploits undermine the technical layer; missing DisabledTheorem |

**Average: 2.8** (below the 3.0 threshold)
**Red flags**: P0 exploits on 6+ levels, draft text in L08, dead inventory item (`tauto`)

---

## 3. Coverage gaps

### 3a. `tauto` is a dead inventory item
`NewTactic tauto` is declared in L09 with a `TacticDoc`, but no level in the world uses `tauto` in its proof script. The learner receives a tactic they never practice and never see demonstrated. This was already flagged in both enrichment reviews (R1 suggestion 1, R2 suggestion 1) but was not fixed.

**Fix**: Either (a) add alternative Branch/Hint paths in L09/L10 showing `ext a; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto` as a shortcut, or (b) remove `NewTactic tauto` from L09 and defer it to a later world where it will actually be used. Option (a) is preferred since it addresses the transfer moment from the plan.

### 3b. Missing `NewTheorem Finset.subset_iff` in L07
L07 teaches subset proofs and references `Finset.subset_iff` in the introduction but never declares it as a `NewTheorem` with `TheoremDoc`. The learner's inventory won't show it.

### 3c. Missing `NewTheorem Finset.ext_iff` in L05
L05 cites `Finset.ext_iff` in the introduction but only declares `NewTactic ext`. A learner wanting to use `rw [Finset.ext_iff]` instead of the `ext` tactic won't find the theorem in inventory.

### 3d. No counterexample or warning level
The world proves 10 positive facts and zero negative ones. No level shows a false generalization (e.g., set difference is not symmetric). Enrichment R1 suggested this (suggestion 2) and it was marked "Yes" but not implemented.

---

## 4. Granularity defects

### 4a. L05 and L06 are structurally identical
Both prove commutativity via `ext + constructor + intro + rw + rcases + rebuild`. L06's only novelty is the angle-bracket conjunction syntax (`rcases h with <hs, ht>` and `exact <ht, hs>`). This is defensible as consolidation but is a missed opportunity. Enrichment R2 suggested changing L06 to the absorption law (`s cap (s cup t) = s`), which would exercise a different proof structure. Classification: P2, not blocking.

### 4b. L08's task description contains draft monologue
Lines 43--54 of L08's introduction read: "Actually, for this level you do NOT need `by_cases` -- this is a warm-up. But the next level will use it. Wait -- let's make this level actually use `by_cases`. Here is a better task:" This is author's internal revision that was never cleaned up. Both enrichment reviews flagged it. Classification: P1 (polish but affects learner trust).

---

## 5. Statement exploitability

### P0 defects (blocking)

| Level | Exploit | Tactic | Severity |
|-------|---------|--------|----------|
| L01 | Bare `simp` closes entire goal | `simp` | P0 |
| L01 | `norm_num` closes entire goal | `norm_num` | P0 |
| L02 | Bare `simp` closes entire goal | `simp` | P0 |
| L02 | `norm_num` closes entire goal | `norm_num` | P0 |
| L03 | Bare `simp` closes entire goal | `simp` | P0 |
| L03 | `norm_num` closes entire goal | `norm_num` | P0 |
| L04 | Bare `simp` closes entire goal | `simp` | P0 |
| L04 | `norm_num` closes entire goal | `norm_num` | P0 |
| L07 | Bare `simp` closes entire goal | `simp` | P0 |
| L08 | Bare `simp` closes entire goal | `simp` | P0 |

**Analysis**: `simp` is deliberately available in this world (the intended proofs use `simp [Finset.mem_insert, Finset.mem_singleton]` to close concrete membership subgoals). But bare `simp` also closes the top-level goals of L01-L04, L07, L08 in a single step, bypassing the membership-lemma rewriting that is the dominant lesson.

**Recommended fix**: Add `simp` to `DisabledTactic` on L01-L04, L07, L08. Replace the `simp [Finset.mem_insert, Finset.mem_singleton]` closing steps with `decide` or explicit membership lemma chains. Alternatively, keep `simp` available but restructure L01-L04 to use abstract finsets (making `simp` unable to close them). The abstract approach is cleaner but requires significant rework.

For `norm_num`: add `norm_num` to `DisabledTactic` on L01-L04. This is a lower-effort fix.

### P1 defects (high)

| Level | Exploit | Tactic/Lemma | Severity |
|-------|---------|--------------|----------|
| L05 | Library lemma one-shot | `exact Finset.union_comm s t` | P1 |
| L06 | Library lemma one-shot | `exact Finset.inter_comm s t` | P1 |
| L07 | Library lemma one-shot | `exact Finset.subset_union_left` | P1 |
| L09 | Library lemma one-shot | `exact Finset.inter_union_distrib_left s t u` | P1 |
| L10 | Library lemma one-shot | `exact Finset.sdiff_inter_distrib_right s t u` | P1 |
| L10 | `ext + simp + tauto` shortcut (3 steps) | `ext a; simp only [...]; tauto` | P1 |

**Analysis**: The library lemma exploits are a standard risk when teaching proofs of well-known theorems. Adding `DisabledTheorem` for each library lemma is the standard fix. The `ext + simp + tauto` shortcut for L10 is a specific consequence of introducing `tauto` in L09.

**Recommended fix**:
- Add `DisabledTheorem Finset.union_comm` on L05
- Add `DisabledTheorem Finset.inter_comm` on L06
- Add `DisabledTheorem Finset.subset_union_left` on L07 (and `Finset.le_sup_left` if it exists as an alias)
- Add `DisabledTheorem Finset.inter_union_distrib_left` on L09
- Add `DisabledTheorem Finset.sdiff_inter_distrib_right` on L10
- For L10: if `tauto` is kept, the `ext + simp + tauto` shortcut is arguably acceptable for the boss since it demonstrates understanding of the `ext` pattern. However, if the boss should force manual proof, consider disabling `tauto` on L10 (re-enabling it afterward).

### P2 defects (medium)

| Level | Exploit | Notes |
|-------|---------|-------|
| L01-L04 | `decide` one-shots | Already disabled -- no issue |

---

## 6. Interactive proof quality

### L05 reverse direction: hint cliff
The reverse direction (lines 83-98) has one visible hint ("The argument is symmetric") and one hidden hint that dumps the ENTIRE solution (5+ tactic steps). There are no intermediate hints. A stuck learner must either (a) figure out all steps independently or (b) reveal a hint that gives the complete solution. This violates the layered-hint principle.

**Fix**: Add per-step hints in the reverse direction of L05, mirroring the forward direction's granularity.

### L06 reverse direction: same issue
Lines 68-76: one visible hint, one hidden hint with the full solution. No intermediate hints.

**Fix**: Add per-step hints in L06's reverse direction.

### L09/L10: proof length vs interactivity
L09's intended proof is ~30 tactic steps. L10's is ~40 tactic steps. Both are well-hinted with per-step guidance, so this is not a defect. However, the length may discourage learners who don't realize the proof is routine at each step. The introductions do warn about length, which helps.

---

## 7. Learner simulation

### Attentive novice

**First stuck point**: L05, after `ext a; constructor; intro h`. The novice has a membership hypothesis `h : a in s cup t` and needs to rewrite it with `mem_union`, but the pattern of rewriting a HYPOTHESIS (using `rw [...] at h`) may not be obvious. The novice may try `rw [Finset.mem_union]` (which rewrites the goal, not the hypothesis). The hints rescue this: the hidden hint says `rw [Finset.mem_union] at h`. But the open hint doesn't explicitly mention `at h` -- it says "Rewrite `h` with `mem_union`" which is ambiguous (does it mean rewrite h or rewrite using h?).

**Most likely wrong move**: In L01, typing bare `simp` and getting the level closed without understanding why. The learner then proceeds through L02-L04 using `simp` everywhere, missing all the membership lemmas. This is the most dangerous exploit because it's silent -- the learner thinks they're progressing when they're learning nothing.

**Hint rescue quality**: Generally good for forward directions. Weak for reverse directions in L05/L06 as noted above. The L08 draft monologue is confusing -- the learner reads about a task they won't actually do.

### Experienced Lean user

**Avoidable friction**: The experienced user will immediately try `exact Finset.union_comm s t` on L05 and close it. They'll do the same for L06, L07, L09, L10. This isn't "friction" per se -- they can clear the world quickly -- but they learn nothing. DisabledTheorem would force engagement.

**Alias gaps**: No major alias gaps. The world correctly uses `Finset.mem_union` etc.

**Inventory clutter**: `tauto` is clutter since it's never used. Otherwise the inventory is clean.

**Needless forced verbosity**: The `rw [Finset.mem_union]` + `left/right` pattern could be shortened to `simp [Finset.mem_union]` + `exact`. But the manual approach is pedagogically correct for a first-contact level. Not a defect.

---

## 8. Boss integrity (L10)

### Seeded subskills
- `ext`: introduced L05, practiced L06, used in L09 -- SEEDED
- `mem_union`: introduced L01, practiced L04, L05, L07, L08, L09 -- SEEDED
- `mem_inter`: introduced L02, practiced L04, L06, L09 -- SEEDED
- `mem_sdiff`: introduced L03, practiced L08 -- SEEDED (minimally -- only 1 practice before boss)
- `by_cases`: introduced L08 -- SEEDED (minimally -- only 1 practice before boss)
- Negation reasoning (`intro hu; apply hntu`): NOT explicitly seeded. The learner encounters proof-by-contradiction for the first time in the boss.

### Boss quality
The boss genuinely integrates the world's techniques. The forward direction requires a novel `by_cases` + negation argument that creates real planning challenge. The reverse direction requires systematic extraction and reconstruction. This is NOT a gauntlet boss -- the interaction between `by_cases` and negation reasoning is genuinely novel.

### Concern: negation reasoning is unseeded
The boss's forward direction (case `ht : a in t`) requires the learner to prove `a notin u` by assuming `a in u` and deriving a contradiction with `hntu`. This proof-by-contradiction pattern is never isolated or practiced before the boss. The hints cover it well (the hidden hint gives the full steps), but this is a hidden prerequisite leak.

**Fix**: Add a brief negation-reasoning level between L08 and L09 (or modify L08 to include a negation subgoal). For example: "Prove that if `a in s \ t` then `a notin t`" which requires `intro ht; have h := ...; exact h.2 ht`.

### Boss exploitability
- `exact Finset.sdiff_inter_distrib_right s t u` -- one-shot (P1, needs DisabledTheorem)
- `ext a; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto` -- 2-step shortcut (P1)
- Without these exploits, the boss requires genuine multi-step reasoning -- good.

---

## 9. Course-role sanity

The world plays its LECTURE role correctly:
- L01-L03: first-contact levels (union, inter, sdiff membership lemmas)
- L04: combining exercise (multi-step membership reasoning)
- L05: first-contact level (ext tactic)
- L06: supported practice (ext on intersection)
- L07: first-contact level (subset proofs)
- L08: first-contact level (by_cases)
- L09: integration exercise (distributivity combining all tools)
- L10: boss (De Morgan's law integrating everything)

The progression from individual operations -> combination -> extensionality -> subset -> case analysis -> integration is natural and well-sequenced.

No role mismatches detected.

---

## 10. Technical risks

1. **Build warnings**: L10 reports missing TacticDoc for `trivial`, `decide`, `native_decide`, `aesop`, `simp_all`. These are inherited from earlier worlds and produce "Using existing docstring" warnings, which are informational but noisy.

2. **`tauto` availability**: Once introduced in L09, `tauto` is available in L10 and all subsequent worlds. Combined with `simp`, it creates a powerful shortcut that can close many finset equality goals. This is fine if intended but should be considered when designing later worlds.

3. **Missing `omega` in DisabledTactic**: `omega` is not disabled but also cannot close any goal in this world (tested). Not a risk currently.

---

## 11. Ranked patch list

| Rank | Severity | Issue | Fix | Levels |
|------|----------|-------|-----|--------|
| 1 | P0 | Bare `simp` one-shots L01-L04, L07, L08 | Either (a) disable `simp` on these levels and rework closing steps, or (b) restructure L01-L04 to use abstract finsets. For L07/L08, disabling `simp` is simpler since the proofs don't use `simp` at all. | L01-L04, L07, L08 |
| 2 | P0 | `norm_num` one-shots L01-L04 | Add `norm_num` to DisabledTactic on L01-L04 | L01-L04 |
| 3 | P1 | Library lemma one-shots on L05, L06, L07, L09, L10 | Add `DisabledTheorem` for `Finset.union_comm`, `Finset.inter_comm`, `Finset.subset_union_left`, `Finset.inter_union_distrib_left`, `Finset.sdiff_inter_distrib_right` | L05, L06, L07, L09, L10 |
| 4 | P1 | L08 contains author's draft monologue | Remove the "Actually... Wait..." paragraph from L08's introduction and present the task directly | L08 |
| 5 | P1 | `tauto` introduced but never used | Add alternative hints in L09/L10 showing `ext + simp + tauto` shortcut, OR remove `NewTactic tauto` and defer to a later world | L09 |
| 6 | P1 | L05/L06 reverse directions have no intermediate hints | Add per-step hints in the reverse direction mirroring the forward direction's granularity | L05, L06 |
| 7 | P1 | Boss negation reasoning is unseeded | Add a brief negation-reasoning exercise before the boss (between L08 and L09, or as an additional subgoal in L08) | L08-L09 |
| 8 | P2 | Missing `NewTheorem Finset.subset_iff` in L07 | Add `NewTheorem Finset.subset_iff` and `TheoremDoc` | L07 |
| 9 | P2 | Missing `NewTheorem Finset.ext_iff` in L05 | Add `NewTheorem Finset.ext_iff` and `TheoremDoc` | L05 |
| 10 | P2 | `mem_sdiff` has minimal practice before boss | Only 1 practice (L08) before L10 uses it extensively. Consider adding an `sdiff` practice level. | L03, L08 |

---

## 12. What to playtest again after patching

After addressing patches 1-7:

1. **Re-run exploit testing** on all 10 levels with `simp`, `norm_num`, `decide`, `tauto`, and library lemma one-shots to verify all exploits are closed.
2. **Re-audit L01-L04** if the closing tactic changes (from `simp` to something else) -- verify the new closing steps are teachable and hint-compatible.
3. **Re-audit L05/L06 reverse directions** after hints are added -- verify they rescue without spoiling.
4. **Re-audit L08** after draft text removal -- verify introduction reads cleanly.
5. **Re-audit L10 boss** after negation-reasoning seeding -- verify the hidden prerequisite leak is closed.
6. **Verify `tauto` usage** if alternative hints are added to L09/L10 -- check that the hints fire in the right context and don't interfere with the manual proof path.
7. **Full learner simulation** of L01 through L10 with a novice profile to verify the world still holds together as a coherent learning sequence after all patches.
