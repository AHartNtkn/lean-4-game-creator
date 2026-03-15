# Enrichment Review (Round 3): W3 ListBasics

This is a third-pass review after aesop and simp bypass fixes. The second review identified 8 suggestions; 4 were marked "Recommend: Yes" and 4 "Recommend: Consider." This review evaluates what was addressed and what remains.

## What was fixed since the second review

The bypass issue that prompted this pass is resolved:

- **aesop** is disabled in all 11 levels via `DisabledTactic`.
- **simp** is disabled in all levels except L01, L08, and L09. In L01 and L08, the intended solution is `rfl` (definitional equality), so allowing `simp` there is harmless -- it cannot shortcut genuine reasoning because there is none to shortcut. In L09, `simp` is deliberately introduced as a `NewTactic` and used to dispatch concrete non-membership goals (`1 not in [2, 3]`), which is its intended pedagogical role.

No level can be bypassed by an automation tactic that skips the intended proof structure.

## Status of R2 suggestions

| R2 # | Summary | R2 Recommend | Status in R3 |
|-------|---------|--------------|-------------|
| 1 | L02 single-step rewrite | Consider | Unchanged |
| 2 | L07 same shape as L02 | Consider | Unchanged |
| 3 | Nodup: no failure case | Yes | Unchanged |
| 4 | No backward membership direction | Yes | Unchanged |
| 5 | `simp` introduced silently | Yes | Partially addressed |
| 6 | L01 is rfl | No action needed | N/A |
| 7 | Boss transfer: no Socratic question | Consider | Unchanged |
| 8 | L08 concrete rfl | Consider | Unchanged |

The "Recommend: Consider" items (1, 2, 7, 8) are defensible design choices in a world that is already at 11 levels and has a clear progression. I will not re-raise them. The "Recommend: Yes" items (3, 4, 5) remain genuine opportunities. I assess them below alongside any new observations.

## Ranked suggestions

### 1. L10 (Practice) should exercise the backward direction of a membership iff -- the learner never destructures a membership hypothesis

**What**: Every membership proof in the world (L03, L04, L05, L06, L10, L11) works in the forward direction: rewrite to unfold membership into a disjunction/conjunction/existential, then choose the right branch. No level starts from `h : a in some_list` and destructures it to learn which case holds.

**Why**: This was R2 suggestion #4, the review's "single most important remaining improvement," and it has not been addressed. The backward direction -- starting from `a in l1 ++ l2` and extracting `a in l1 or a in l2`, then case-splitting -- is the proof move the learner will use most in downstream worlds. In W6-W8 (finset membership, filter, image), proofs regularly start from `h : a in s` and destructure to understand how `a` got into `s`. If the learner has never done this at the list level, they will encounter it as a new idea at the finset level, when the focus should be on finset-specific content.

L10 is the natural place. Its current proof (forward-direction combination of `mem_cons` and `mem_append`) is fine practice but teaches no new proof move. Replacing it with a statement like `a in l1 ++ l2 -> a in l2 ++ l1` would require destructuring the hypothesis (backward: `rw [List.mem_append] at h` or `rcases List.mem_append.mp h with h1 | h2`), then reassembling in the other order (forward: `rw [List.mem_append]`, `left`/`right`). This exercises both directions in a single level.

**Where**: L10 (Practice). Modify the statement and proof.

**Effort**: Medium (rewriting one level).

**Recommend**: Yes. This is the most important remaining gap.

---

### 2. L09 (Nodup) only shows the success case -- the learner never experiences what happens when duplicates are present

**What**: L09 proves `[1, 2, 3].Nodup`. The conclusion explains that `[1, 2, 1].Nodup` would fail because `1 in [2, 1]`, but the learner never works through the failure.

**Why**: This was R2 suggestion #3, marked "Recommend: Yes." The plan specifies W3.7 as "Prove a specific list has no duplicates, and show one that does [have duplicates]." Seeing a definition succeed is necessary; seeing it fail is what builds understanding. The current implementation covers only the success side.

A clean fix that avoids adding a 12th level: add a second `Statement` in L09 (a two-goal level) where the learner proves `1 in [2, 1]` -- the fact that blocks `[1, 2, 1].Nodup`. The conclusion then connects these: "You proved `1 in [2, 1]`, which means `List.nodup_cons` applied to `[1, 2, 1]` would require `1 not in [2, 1]` -- but you just showed the opposite. So `[1, 2, 1]` has duplicates."

Alternatively, the second goal could be `not [1, 2, 1].Nodup`, proved by `simp [List.nodup_cons]` (since `simp` is already enabled in L09).

**Where**: L09 (Nodup). Add a second goal or split into L09a/L09b.

**Effort**: Medium (adding a second statement to one level).

**Recommend**: Yes. The plan explicitly calls for the failure case.

---

### 3. The `simp` introduction in L09 could be more explicit

**What**: L09 introduces `simp` as a `NewTactic` with a `TacticDoc`, and the hint says "For this concrete membership check, `simp` can evaluate it. Try `simp`." But the introduction never mentions `simp` at all -- the learner encounters it only mid-proof in a hint.

**Why**: This was R2 suggestion #5, marked "Recommend: Yes." The hint has been improved slightly (it now says "can evaluate it" rather than just "try `simp`"), which is better than the R2 state. However, the introduction still does not mention `simp`. For a tactic as central as `simp`, the learner should know *before* they need it that it exists and what it does.

The fix is two sentences in the introduction, after the "Your task" section: "For the concrete non-membership checks, you will use a new tactic: `simp`. This tactic simplifies the goal using a database of known lemmas -- here, it knows facts like `1 != 2` and `1 != 3`, so it can verify `1 not in [2, 3]` automatically. You will use `simp` extensively in later worlds."

**Where**: L09 (Nodup), introduction text.

**Effort**: Low (two sentences in an introduction).

**Recommend**: Yes. `simp` should not be introduced only in a hint.

---

### 4. The Nodup conclusion's claim about `[1, 2, 1]` could cite the exact spot where the proof would get stuck

**What**: The L09 conclusion says "1 in [2, 1]" but does not show the learner the exact step. It says the proof "would be stuck" without showing the stuck goal state.

**Why**: If suggestion #2 above is adopted (adding the failure-case goal), this becomes moot. If not, the conclusion should be more precise: "Applying `rw [List.nodup_cons]` to `[1, 2, 1].Nodup` gives the goal `1 not in [2, 1] and [2, 1].Nodup`. But `1 in [2, 1]` is true (since `1` is in the tail), so `1 not in [2, 1]` is false. No tactic can prove a false statement, so the proof is stuck." This shows the learner the *mechanism* of failure rather than just asserting it.

**Where**: L09 (Nodup), conclusion text.

**Effort**: Low (expanding a paragraph in the conclusion).

**Recommend**: Consider. Only relevant if suggestion #2 is not adopted.

---

## Overall impression

The world is in strong shape. The two rounds of revision have addressed all critical issues from the original review: genuine proof reasoning throughout, `Nodup` present, `Fin`-indexing connecting to W1, map and filter used symbolically, the boss integrating multiple operations in a multi-step proof, and aesop/simp bypasses eliminated. The level ladder has a clean progression from notation through symbolic rewriting, membership lemmas with disjunctions/existentials/conjunctions, structural properties, practice, and boss integration. The writing is consistently clear, with good foreshadowing, honest "in plain language" summaries, and well-targeted hints.

Two genuine gaps remain. The more important one is the absence of backward membership reasoning (suggestion #1): the learner can *prove* membership from components but never *uses* a membership hypothesis by destructuring it, which is the dominant proof move in downstream finset worlds. The second is the Nodup failure case (suggestion #2): the plan specifies it, and telling the learner about failure is not the same as letting them experience it. Both can be addressed within the existing 11-level structure by modifying L10 and L09 respectively. The `simp` introduction (suggestion #3) is a low-effort fix that would improve the pedagogical completeness of L09.

If these three items are addressed, the world is clean.
