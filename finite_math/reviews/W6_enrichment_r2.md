# W6 FinsetMembership -- Enrichment Review (Round 2)

## Changes since R1

- Added `NewTactic rcases` + `TacticDoc rcases` to L08 (DestructuringMembership).
- Fixed terminology in L06: now says "absorption" instead of "idempotency." Conclusion explicitly names the absorption law and contrasts List vs Finset duplicate behavior.
- Boss (L09) already uses `simp` in Parts A, B, and C (R1 was incorrect that `simp` was absent from the boss).

## R1 disposition

| R1 # | Item | Status | Notes |
|-------|------|--------|-------|
| 1 | L08 missing `NewTactic rcases` + `TacticDoc rcases` | **Fixed** | L08 now has both. The `TacticDoc rcases` block is detailed and covers disjunctions, `rfl` patterns, and nested patterns. Well written. **Closed.** |
| 2 | L06 should use "absorption" not "idempotency" | **Fixed** | L06's title is now "insert absorbs duplicates." The introduction uses "leaves the set unchanged," the lemma is `insert_eq_of_mem`, the conclusion names the absorption law and contrasts List vs Finset. The terminology is now precise and pedagogically clear. **Closed.** |
| 3 | Boss should use `simp` in all parts | **Not applicable** | R1 was factually wrong -- the boss already used `simp [Finset.mem_insert, Finset.mem_singleton]` in Parts A, B, and C. No change was needed. **Closed.** |

---

## New ranked suggestions

### 1. L07 (NonMembership) does not teach `intro` for negation goals

**What**: L07 proves `4 ∉ ({1, 2, 3} : Finset Nat)` using `simp` alone, but the conclusion shows a manual proof that starts with `intro h`. The learner never actually *executes* an `intro` on a negation goal (`∉` is `¬(∈)` which is `∈ → False`). This is the first time in the course that the learner encounters a negation-as-implication goal, and the proof pattern is delegated entirely to `simp`.

**Why**: In L08, the learner must use `rw [...] at h` and `rcases`, but these operate on a *given* hypothesis. The manual non-membership proof in L07's conclusion shows a fundamentally different proof shape: `intro h` to *assume* membership, then derive contradiction. This "assume and contradict" pattern is the standard approach for non-membership in ordinary mathematics. By having `simp` close L07 in one step, the learner never practices the pattern that the conclusion describes. The learner reads about it but never does it.

A two-part level (or a modified single-part) could have the learner first prove non-membership manually (`intro h` / rewrite / `rcases` / `omega` or `contradiction`) and then re-prove it with `simp` -- mirroring L05's "manual vs automated" structure. Alternatively, the manual proof could be a separate level before L07, with L07 reserved for the `simp` shortcut.

**Where**: L07

**Effort**: Medium (either split L07 into two parts with `constructor`, or add a new level before L07 for the manual proof and rename)

**Recommend**: Yes -- the "intro on negation" proof move will be needed in W7 (subset proofs via `intro`) and throughout the rest of the course. L07 is the natural place to teach it, and currently it is only shown, not practiced.

---

### 2. L08 uses `omega` without introduction or `NewTactic`

**What**: L08's proof closes three arithmetic impossibility goals (`1 < 4`, `2 < 4`, `3 < 4`) with `omega`, and the conclusion's manual non-membership example also uses `omega`. But `omega` is never declared via `NewTactic omega` in this world or (as far as this review can determine) in earlier worlds. The learner is told to use `omega` without it being in their inventory.

**Why**: `omega` is a powerful decision procedure for linear arithmetic over naturals and integers. A learner encountering it for the first time in L08 will not know what it does, when it applies, or what its limitations are. The hints say "use `omega`" but never explain that `omega` is a tactic that solves linear arithmetic goals automatically. Even a one-sentence explanation in the first hint that references `omega` ("The tactic `omega` automatically solves goals involving linear arithmetic -- equalities, inequalities, and non-equalities over natural numbers") would make the introduction less abrupt. Adding `NewTactic omega` and a `TacticDoc omega` block would make it properly part of the inventory.

If `omega` was introduced in an earlier world (W1-W5), then `NewTactic` is not needed again -- but the current world should still remind the learner what it does, since this is the first time `omega` is used to close *contradiction goals* (e.g., showing `4 = 1` is impossible) rather than proving an arithmetic fact.

**Where**: L08

**Effort**: Low (add `NewTactic omega` + `TacticDoc omega` if not introduced earlier; or add a sentence in L08's first `omega` hint explaining what it does)

**Recommend**: Yes -- undeclared tactic use is an inventory gap.

---

### 3. L06 proves absorption but never states non-absorption (inserting a new element changes the finset)

**What**: L06 teaches `Finset.insert_eq_of_mem`: if `a ∈ s`, then `insert a s = s`. But the converse direction -- if `a ∉ s`, then `insert a s ≠ s` (or equivalently, `(insert a s).card = s.card + 1`) -- is never mentioned.

**Why**: Absorption is one half of the `insert` story. The other half is that inserting a *genuinely new* element does change the finset. Without this, the learner might (correctly) wonder: "does `insert` ever actually do anything?" The complement to `insert_eq_of_mem` is `Finset.card_insert_of_not_mem` (which may have been taught in W5), or the simpler `Finset.insert_ne_self_of_not_mem`. A brief mention in L06's conclusion -- "what happens when the element is *not* already present?" with a forward reference to W7's cardinality work or a reminder of W5's cardinality peeling -- would complete the picture.

**Where**: L06 conclusion

**Effort**: Low (add 2-3 sentences to the conclusion)

**Recommend**: Consider -- the information exists elsewhere in the course, but L06 is where the learner thinks about insert behavior and the question naturally arises.

---

### 4. The world has no level where `simp` fails and the learner must fall back to manual rewriting

**What**: L04 introduces `simp`; L05 shows `simp` vs manual but lets `simp` succeed; L06-L07 use `simp` for membership subgoals; L08 introduces manual destructuring but for a different reason (symbolic `x`). There is no level where `simp` is tried, fails (or is insufficient), and the learner must use manual `rw` to make progress.

**Why**: L05's conclusion says "save manual reasoning for when you need to understand *why* something is a member," and L05's intro lists three reasons to prefer manual rewriting. But the learner never encounters a situation where `simp` actually fails. L08 is the closest, but there `simp` is not attempted -- the learner is told upfront that the goal is symbolic and needs case analysis. A level where the learner has a goal like `a ∈ insert a s` (with `a` and `s` as variables) where `simp` cannot close the goal (because it does not know that `a = a` is the left disjunct) and the learner must use `rw [Finset.mem_insert]` followed by `left; rfl` would drive home the manual/automated boundary that L05 discusses abstractly.

**Where**: New level between L05 and L06 (or modify L05 to have a two-part structure: first solve with `simp`, then solve a symbolic goal manually)

**Effort**: High (add a new level)

**Recommend**: Consider -- L08 partially addresses this (symbolic membership requiring manual work), but L08's focus is on destructuring a hypothesis, not on proving a symbolic membership goal. The gap is real but not critical, since W7 will require `ext` proofs where `simp` alone is insufficient.

---

### 5. Boss Part B uses exhaustive `rw`/`rcases` when `simp` could close it

**What**: Boss Part B proves `∀ x, x ∈ ({1, 2, 3} : Finset Nat) → x ∈ ({0, 1, 2, 3, 4} : Finset Nat)` by case-splitting `hx` into three concrete cases. But after `intro x hx`, `simp [Finset.mem_insert, Finset.mem_singleton] at hx` would give `hx : x = 1 ∨ x = 2 ∨ x = 3`, and then `rcases hx with rfl | rfl | rfl` followed by `simp [Finset.mem_insert, Finset.mem_singleton]` would be shorter. Alternatively, the entire Part B could be closed by `intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; rcases hx with rfl | rfl | rfl <;> simp [Finset.mem_insert, Finset.mem_singleton]`.

**Why**: The boss's purpose is to integrate all techniques. Part B integrates `rw at h` + `rcases` (from L08) with `simp` (from L04). This is good. But the current proof manually peels each `insert` layer with `rw [Finset.mem_insert] at hx` three times. The learner already saw this pattern in L08 and does it identically here. A more efficient approach -- using `simp at hx` to flatten the membership into a three-way disjunction in one step -- would demonstrate a new technique: using `simp` to simplify a *hypothesis* (not just a goal). This "simp at h" pattern is extremely useful throughout the rest of the course and is not taught anywhere in the current world.

That said, the current approach is pedagogically defensible: it reinforces the L08 pattern in a harder setting and shows the learner what `simp` is doing under the hood. The boss should probably accept *either* approach. A hint could mention the `simp at hx` shortcut after the learner has started the manual approach.

**Where**: L09 (Boss) Part B

**Effort**: Low (add a hint mentioning `simp [Finset.mem_insert, Finset.mem_singleton] at hx` as an alternative after the first `rw`)

**Recommend**: Consider -- teaching `simp at h` here would preview a technique used heavily in W7+. But adding it as an alternative hint (not the canonical solution) avoids changing the boss's structure.

---

### 6. L01's `TheoremDoc` for `Finset.mem_insert` could mention that it is a biconditional (`↔`)

**What**: The `TheoremDoc` for `Finset.mem_insert` says "An element belongs to `insert b s` exactly when it equals `b` or it already belonged to `s`." This is correct, but the entry does not explicitly note that the `↔` means both directions are available: you can `rw` with it to go from `a ∈ insert b s` to the disjunction, *and* from the disjunction back to membership.

**Why**: In L08, the learner uses `rw [Finset.mem_insert] at h` -- the right-to-left direction on a hypothesis. The learner who reads `mem_insert` as a one-way simplification rule might be surprised that `rw` works on hypotheses with it. A sentence like "Because this is a biconditional (`↔`), `rw` can apply it in either direction and on either goals or hypotheses" would prepare the learner for L08's technique.

**Where**: L01 `TheoremDoc Finset.mem_insert`

**Effort**: Low (add one sentence)

**Recommend**: Consider -- the bidirectionality of `↔` and `rw` was likely taught in earlier courses (NNG4 level). This is reinforcement.

---

### 7. The world conclusion (L09) does not mention `omega`

**What**: L09's conclusion lists what the learner learned: `mem_insert`, `mem_singleton`, `simp` with lemma lists, `insert_eq_of_mem`, non-membership, and `rw [...] at h` + `rcases`. But `omega` is not listed, despite being used in L08 (three times) and in L07's conclusion example.

**Why**: Even if `omega` is not the focus of any level, it was used as a workhorse tactic. Listing it in the conclusion's inventory summary ensures the learner's mental model of "what tools I now have" is complete.

**Where**: L09 conclusion

**Effort**: Low (add one bullet point)

**Recommend**: Yes -- it is an omission in the summary.

---

## Overall impression

The world is well-structured. The level ladder from manual membership verification (L01-L03) through `simp` automation (L04-L05) to absorption (L06), non-membership (L07), symbolic destructuring (L08), and the integrative boss (L09) is pedagogically sound and follows a clear arc. The prose is consistently high quality: introductions frame the problem, conclusions include "in plain language" summaries, and the transfer section in L09 connects Lean techniques to paper-proof reasoning. The R1 items have been addressed: `rcases` is now properly introduced, and the absorption terminology is correct.

The single most important improvement is **suggestion #1**: L07 should have the learner actually *execute* an `intro h` on a negation goal before `simp` closes it. The "assume and derive contradiction" pattern for negation is fundamental to mathematical reasoning, and L07 is the only level in the world where it naturally arises. Currently the learner reads about it in the conclusion but never does it. This is a proof-move gap, not a content gap -- the kind of thing that matters most for transfer. Close behind is **suggestion #2** (`omega` inventory gap), which is a concrete fix requiring minimal effort.
