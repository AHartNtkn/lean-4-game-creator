# W6 FinsetMembership — Enrichment Review (Round 1)

## Ranked suggestions

### 1. The manual non-membership proof pattern is described but never practiced

**What**: L07 explains the manual `intro h; rw [...] at h; rcases; omega` approach to non-membership in the conclusion but only asks the learner to use `simp`. The learner never actually practices the manual non-membership proof.

**Why**: This is the most impactful gap in the world. Non-membership is introduced one level before destructuring membership (L08), and L08 teaches `rw [...] at h` + `rcases` — but only for *positive* membership hypotheses. The manual non-membership pattern is a natural bridge between L07 and L08: it uses the same `rw [...] at h` + `rcases` + `omega` move, but in a contradiction context (`intro h` first, then destructure). By skipping the manual practice, L07 deprives L08 of a setup exercise. The conclusion of L07 literally says "the manual approach previews a technique you will use soon" — but the learner never gets to execute that preview. This is a scaffold promise that goes unfulfilled.

**Where**: Add a new level between current L07 and L08, or split L07 into two levels: L07a (manual non-membership) and L07b (`simp` non-membership). The manual version should come first so the learner appreciates what `simp` automates.

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. `simp` is taught without `NewTactic` declaration

**What**: L04 introduces `simp` as a new tactic but there is no `NewTactic simp` declaration visible in L04 or any earlier level in this world. Additionally, there is no `TacticDoc` entry for `simp` in any level of this world.

**Why**: The course has an established standard (from MEMORY.md lessons learned) of always declaring `NewTactic` for tactics used in hints and always adding `TacticDoc` for disabled tactics. `simp` is the dominant new tactic of this entire world — it is introduced in L04, disabled in L01-L03, and re-enabled from L04 onward. If there is no `NewTactic simp` declaration, the inventory panel will not show `simp` as a newly available tool when the learner reaches L04. This breaks the inventory release system.

**Where**: L04 (add `NewTactic simp` and a `TacticDoc` entry for `simp`).

**Effort**: Low (add two declarations).

**Recommend**: Yes.

---

### 3. L01-L03 teach a "scan from left to right" pattern but never name it

**What**: L01, L02, and L03 each use the pattern "apply `mem_insert`, choose `left`/`right`, repeat or base-case with `mem_singleton`." L03's conclusion calls this a "complete manual proof pattern" and gives a numbered recipe. But the strategy is never given a memorable name that can be referenced later.

**Why**: Named strategies transfer better than unnamed ones. The conclusion of L03 describes the pattern well but calls it "the manual proof pattern" — a generic label. A name like "the membership scan" or "peel-and-match" would give the learner a mental handle. L05's conclusion references "the manual approach" and the boss references "the rw [...] at h + rcases pattern" — but none of these are the same named thing. Naming the strategy in L03 and referencing it by name in L05, L08, and the boss conclusion would create a throughline.

**Where**: L03 conclusion (name it), then L05/L08/L09 conclusions (reference the name).

**Effort**: Low (text changes in conclusions).

**Recommend**: Yes.

---

### 4. No level explores `mem_insert` as an iff (both directions)

**What**: `Finset.mem_insert` is an iff: `a ∈ insert b s ↔ a = b ∨ a ∈ s`. L01-L03 only use it in the left-to-right direction (rewriting a membership goal into a disjunction). L08 uses the right-to-left direction implicitly (rewriting a hypothesis). But no level explicitly teaches that `mem_insert` is bidirectional and that `rw` works at hypotheses because it is an iff.

**Why**: The iff nature of `mem_insert` is the reason the same lemma works in both directions. In L01-L03, `rw [Finset.mem_insert]` rewrites a goal `a ∈ insert b s` into `a = b ∨ a ∈ s`. In L08, `rw [Finset.mem_insert] at h` rewrites a hypothesis the same way. The learner may not realize this is the same lemma doing the same thing in a different position. An explicit moment where both directions are shown — or where the learner must use the iff to go from `a = b ∨ a ∈ s` back to `a ∈ insert b s` — would deepen understanding.

**Where**: A brief level between L03 and L04 (before `simp` takes over), or a remark in L08's introduction.

**Effort**: Medium (could be a new level, or could be woven into L08's intro as an explicit teaching point).

**Recommend**: Consider.

---

### 5. L06 does not explore the converse of `insert_eq_of_mem`

**What**: L06 teaches `insert_eq_of_mem : a ∈ s → insert a s = s`. The converse direction — "if `insert a s = s`, then `a ∈ s`" — is also true and is `Finset.mem_of_insert_eq`. This equivalence is never mentioned.

**Why**: The converse is a derivable result that illuminates idempotency from the other direction. A learner might wonder: "If I know `insert a s = s`, can I conclude `a ∈ s`?" This is a natural "what if?" question that L06 could address in its conclusion, even without a dedicated level. At minimum, mentioning it shows the learner that the relationship between membership and insertion is tight: `a ∈ s` iff `insert a s = s`.

**Where**: L06 conclusion (add a remark about the converse).

**Effort**: Low (one paragraph in the conclusion).

**Recommend**: Consider.

---

### 6. No level uses `Finset.not_mem_singleton` or the `∉` form of `mem_singleton`

**What**: L07 teaches non-membership for multi-element finsets, but the simplest non-membership fact — `a ∉ {b}` when `a ≠ b` — is never isolated. The lemma `Finset.not_mem_singleton` (or the negation of `mem_singleton`) is the natural base case for non-membership, just as `mem_singleton` is the base case for membership.

**Why**: L03 introduces `mem_singleton` as the base case for positive membership. There is no corresponding base case for negative membership. In L07, `simp` handles non-membership in `{1, 2, 3}` as a black box. If the world had a level (or a remark) establishing `a ∉ {b} ↔ a ≠ b` explicitly, the structural parallel between membership and non-membership would be clearer. This would reinforce the "base case / inductive case" structure that the world teaches for positive membership.

**Where**: Before L07 or as part of L07's introduction.

**Effort**: Medium (a new level or significant expansion of L07).

**Recommend**: Consider.

---

### 7. The boss does not test the "membership scan" (manual `mem_insert` + `mem_singleton`) at all

**What**: The boss (L09) tests three things: double idempotency (`insert_eq_of_mem`), containment by exhaustion (`rw [...] at h` + `rcases`), and non-membership (`simp`). But it never tests the most basic skill from L01-L03 — proving `a ∈ {x₁, ..., xₙ}` by manual `rw [mem_insert]` + `left/right` + `rfl/mem_singleton`. Parts A and C both use `simp` for membership.

**Why**: L01-L03 are three full levels dedicated to the manual membership scan. If the boss lets the learner use `simp` for all membership subgoals, the manual skill is never integrated or retrieved. A learner could reach the boss having forgotten the manual technique entirely. The boss should include at least one subgoal where `simp` is not available or where the manual scan is the expected proof path, to ensure retrieval of the L01-L03 skill.

**Where**: Modify Part A or Part C of the boss, or add a Part D that requires manual membership proof (possibly by disabling `simp` for that branch, or by having a symbolic membership goal that `simp` cannot handle).

**Effort**: Medium (modify boss structure or add a branch).

**Recommend**: Yes.

---

### 8. Cross-world foreshadowing: W7's `ext` tactic is not previewed

**What**: The conclusion of L09 mentions that the next world covers "union, intersection, and difference" and the `ext` tactic. But it does not explain *why* `ext` will be needed or connect it to anything from this world.

**Why**: The membership reasoning in this world (especially the exhaustive case analysis in L08 and Part B of the boss) is the foundation for `ext` proofs. An `ext` proof of `s = t` works by showing `∀ x, x ∈ s ↔ x ∈ t` — which is exactly the kind of membership reasoning this world teaches. A sentence in the boss conclusion connecting "exhaustive membership analysis" to "proving two finsets are equal by checking membership element-by-element" would seed the vocabulary for W7 and make the transition smoother.

**Where**: L09 conclusion (add a sentence connecting membership reasoning to extensionality).

**Effort**: Low (one or two sentences).

**Recommend**: Yes.

---

### 9. L05 ("simp vs manual") only asks for `simp`, never for the manual proof

**What**: L05 is titled "simp vs manual rewriting" and its introduction discusses both approaches. But the level only asks the learner to use `simp`. The manual approach is described in the introduction but never practiced in this level.

**Why**: A comparison level should ideally let the learner experience both sides. If the level only asks for `simp`, the "vs" in the title is a false promise — the learner does not actually compare. One option: have two parts (prove the same fact first manually, then with `simp`). Another option: since L01-L03 already cover manual proofs extensively, a remark in the conclusion acknowledging that "you already proved facts like this manually in L01-L03" would make the comparison explicit without requiring redundant work.

**Where**: L05 (modify the conclusion to explicitly reference L01-L03 as the manual comparison, or restructure as a two-part level).

**Effort**: Low (conclusion text) to Medium (restructure level).

**Recommend**: Consider.

---

### 10. `omega` appears in L08 without `NewTactic` or explanation

**What**: L08 uses `omega` to close arithmetic goals (`1 < 4`, `2 < 4`, `3 < 4`) in the proof and hints. But `omega` is not introduced with a `NewTactic` declaration or explanation in this level. The plan says `omega` is an NNG4 baseline tactic (L5), so it may already be available, but its use here is never motivated.

**Why**: A learner encountering `omega` for the first time in this level would not know what it does. If it is already known from earlier worlds (W1 per the plan), a brief reminder in L08's introduction ("recall that `omega` closes concrete arithmetic goals") would refresh the learner's memory. If it has not been declared yet, a `NewTactic omega` is needed.

**Where**: L08 introduction (add a reminder sentence about `omega`).

**Effort**: Low (one sentence).

**Recommend**: Consider.

---

## Overall impression

The world has a clear and well-paced structure. The progression from manual membership proofs (L01-L03) through `simp` automation (L04-L05) to idempotency (L06), non-membership (L07), destructuring (L08), and the integrative boss (L09) is logical and pedagogically sound. The introductions are excellent — they explain both the "what" and the "why," and the conclusions consistently translate the Lean proof into plain language, which is a strong transfer practice. The hint system appears well-scaffolded with progressive reveal.

The single most important improvement is **Suggestion 1**: the manual non-membership proof should be practiced, not just described. L07 describes it, L08 uses the same technique in a different context, but the learner never actually executes a manual non-membership proof. Adding this practice level would complete the symmetry between positive and negative membership reasoning and fulfill the scaffold promise made in L07's conclusion. A close second is **Suggestion 7** (boss retrieval of the manual scan), which would ensure L01-L03's core skill is not lost to `simp` convenience by the end of the world.
