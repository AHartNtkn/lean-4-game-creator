# W8_ex FinsetExploration — Enrichment Review (Round 2)

## R1 disposition

The R1 enrichment review for this world was not persisted to disk; the only reported change since R1 is:

- **Added `NewTactic rintro ring` + `TacticDoc rintro` + `TacticDoc ring` to L04.**

This is confirmed present in the current L04 (lines 103-123). No other R1 items are available to disposition, so this round functions as a comprehensive fresh review.

---

## Ranked suggestions

### 1. L07 boss has no `NewTactic` or hint for `refine`, but `refine` is the very first thing the learner must type

**What**: L07's proof begins with `refine ⟨?_, ?_, ?_, ?_⟩` (line 52), and the first hint tells the learner to use it. But `refine` is never declared via `NewTactic` in this world or any earlier level of this world. While `refine` may have been introduced in a prior world, the learner has not used it inside FinsetExploration. The hint says "Use `refine ⟨?_, ?_, ?_, ?_⟩`" but the tactic has never been practiced in the context of finset operations.

**Why**: `refine` with anonymous goals (`?_`) is a sophisticated tactic usage. The learner has used `constructor` throughout this world (L01, L02, L04, L06) and would naturally reach for `constructor` to split a four-part conjunction. The boss level jumps from `constructor` (binary splitting) to `refine` (n-ary splitting) without any intermediate level or explanation of why `refine` is preferable here. This creates a cold-start for the boss's opening move. Either (a) add a `NewTactic refine` declaration and a `TacticDoc refine` in an earlier level, or (b) change the first hint to say "Use `constructor` repeatedly" and show `refine` as an efficiency alternative in a hidden hint.

**Where**: L07 — add `NewTactic refine` and `TacticDoc refine`, or restructure hints.

**Effort**: Low (add declarations and adjust hint text).

**Recommend**: Yes.

---

### 2. L01's proof is extremely long (34 lines of proof code) with 10 Hints — the second goal's proof should be simplified or the level should be split

**What**: L01 asks the learner to prove a conjunction whose second part (`Finset.image (· + 1) (Finset.range 5) = {1, 2, 3, 4, 5}`) requires `ext x`, `simp only [...]`, `constructor`, `rintro ⟨a, ha, rfl⟩; omega`, and `rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩`. This is a heavyweight proof for Level 1 of an exploration/example world. The learner encounters `rintro` with destructuring patterns, `omega`, the `⟨_, by omega, rfl⟩` anonymous constructor, and `<;>` combinator — all in the very first level.

**Why**: An exploration world should make the learner feel fluent with known tools on concrete objects. L01's second goal introduces complexity that rivals or exceeds the FinsetTransformations boss (W8 L08). The first goal (definitional `rfl`) is elegant and appropriate. The second goal could be simplified: `Finset.image (· + 1) (Finset.range 5) = {1, 2, 3, 4, 5}` should be provable by `ext; simp [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]; omega` — a three-tactic proof matching the pattern of L03. If the current `omega` doesn't close it after `simp only`, try `simp` (without `only`) or `decide`. If the goal truly requires the full `rintro` decomposition, this level is too hard for its position.

**Where**: L01 — simplify the proof of the second conjunct, or split L01 into two levels.

**Effort**: Medium (restructure one level or split into two).

**Recommend**: Yes.

---

### 3. `rintro` is declared as `NewTactic` in L04 but was already used in L01's proof and hints

**What**: L04 declares `NewTactic rintro ring` (line 122), and `TacticDoc rintro` (lines 103-113). But L01 already uses `rintro ⟨a, ha, rfl⟩` (line 78) and `rintro (rfl | rfl | rfl | rfl | rfl)` (line 79), and the L01 hints explicitly guide the learner to use `rintro` (lines 74-76).

**Why**: A `NewTactic` declaration is supposed to mark the first time a tactic enters the learner's inventory. If `rintro` is used in L01 but not declared until L04, either (a) the learner doesn't know `rintro` exists when L01 asks them to use it, which creates frustration, or (b) `rintro` was introduced in a prior world, in which case the L04 `NewTactic` declaration is redundant and should be removed. Either way, there is an inconsistency. If `rintro` was introduced earlier (in FinsetTransformations W8 L08 or FinsetOperations), remove `NewTactic rintro` from L04. If it was NOT introduced earlier, move the `NewTactic rintro` declaration and `TacticDoc rintro` to L01.

**Where**: L01 and L04 — resolve the `NewTactic rintro` placement.

**Effort**: Low (move declarations).

**Recommend**: Yes.

---

### 4. L02 teaches only the positive membership pattern — a non-membership level using direct reasoning (not `simp`) would be more instructive

**What**: L02 proves both `3 ∈ {1,2,3,4,5}` and `6 ∉ {1,2,3,4,5}` using the same tactic: `simp [Finset.mem_insert, Finset.mem_singleton]`. Both goals are closed identically. The learner does not see the structural difference between proving membership (find the matching disjunct) and proving non-membership (refute every disjunct).

**Why**: In the FinsetTransformations world, the learner already used `simp` for membership. The exploration world should deepen understanding, not just repeat `simp`. The non-membership direction is structurally different: to show `6 ∉ {1,2,3,4,5}`, one must show `6 ≠ 1 ∧ 6 ≠ 2 ∧ ... ∧ 6 ≠ 5`. Having the learner unfold this with `intro h`, `simp only [Finset.mem_insert, Finset.mem_singleton] at h`, and then `omega` (or case-split on `h`) would expose the proof structure that `simp` hides. The conclusion even explains this structure ("Under the hood...") but the learner never actually does it. An exploration world should make the learner *do* what the conclusion *describes*.

**Where**: L02 — change the non-membership proof to avoid bare `simp`, or add a note in the hint offering the manual approach as an alternative.

**Effort**: Medium (modify one proof and its hints).

**Recommend**: Consider.

---

### 5. L05 (powerset) and L06 (product) are "preview" levels that introduce operations without fully teaching them — the world should acknowledge this more explicitly in the introduction

**What**: L05 introduces `Finset.powerset` and L06 introduces `Finset.product`, both labeled as "previews." The world introduction (L01) says "you will apply every finset operation you have learned so far" — but powerset and product are new operations the learner has *not* learned before. There is a tension between the world's stated promise (apply known operations) and its actual content (introduce two new operations).

**Why**: A learner entering this world expects to practice, not learn new material. Encountering `Finset.powerset` and `Finset.product` for the first time — with `NewDefinition` and `NewTheorem` declarations — may feel unexpected. The introduction should mention that the world also *previews* two operations (powerset and product) in addition to revisiting known ones (filter, image, range). This sets accurate expectations.

**Where**: L01 introduction text — add a sentence about the preview levels.

**Effort**: Low (text edit).

**Recommend**: Yes.

---

### 6. The boss (L07) does not reference the proof techniques from L01-L06 by level name — the integration is implicit rather than explicit

**What**: L07's introduction lists the technique source ("L03: `ext` + `simp` + `omega`", "L04: `ext` + `simp` + case analysis", etc.), which is good. But the hints within the proof do not reference the earlier levels. The learner gets generic hints rather than "Recall the pattern from Level 3." This is a missed reinforcement opportunity.

**Why**: A boss level is supposed to test whether the learner can recall and combine earlier skills. When hints say "Show the cardinality of the even-filtered finset is 2" without saying "Use the same approach as Level 3 (filter the evens)," the hint misses a chance to activate the learner's memory of the earlier level. Adding a cross-reference costs one phrase and strengthens the integration.

**Where**: L07 hints — add level cross-references.

**Effort**: Low (text additions to existing hints).

**Recommend**: Consider.

---

### 7. No transfer moment for `Finset.range` — L01 introduces it as `NewDefinition` but the conclusion doesn't articulate a transfer statement

**What**: L01 is the first level to introduce `Finset.range` via `NewDefinition Finset.range`. The conclusion mentions that "the range-and-shift construction is the standard way to build arithmetic sequences as finsets" and that "you will see `Finset.range n` extensively when working with big operators." But there is no transfer statement articulating what `Finset.range` means in ordinary mathematics (e.g., "In ordinary math, {0, 1, ..., n-1} is the first n natural numbers. In Lean, this set is `Finset.range n`.").

**Why**: The plan (W8_ex L7) explicitly assigns coverage item T8 (transfer for finset operations). The conclusion's "In plain language" sentence addresses the shift construction but not `Finset.range` itself. Since `Finset.range` will be used heavily in the cardinality and big-operator worlds, a clear transfer statement here would help the learner build a mental model early.

**Where**: L01 conclusion — add a transfer sentence for `Finset.range`.

**Effort**: Low (one sentence).

**Recommend**: Consider.

---

### 8. L03 and L04 both use the `ext` + `simp only [...]` pattern but never name it as a reusable strategy

**What**: L03 (filter) and L04 (image) both follow the same proof structure: `ext x`, then `simp only [...]` to reduce to arithmetic, then close. L01's second goal also uses this pattern. The conclusion of L03 describes the three-step pattern (ext, simp, omega) but never gives it a name.

**Why**: This is the "finset equality by extensionality" strategy, and it appears three times in seven levels. Naming it explicitly (e.g., "**Strategy: ext-and-simplify.** To prove two finsets are equal, use `ext` to reduce to membership, simplify with the relevant `mem_*` lemmas, and close with arithmetic or case analysis.") would make it a referenceable proof move. The boss level (L07) expects the learner to deploy this strategy for Parts 1 and 2 without prompting — a name would help.

**Where**: L03 conclusion — name the strategy prominently. L07 hints — reference by name.

**Effort**: Low (text edits in two places).

**Recommend**: Consider.

---

### 9. L05 proves a cardinality fact (`powerset.card = 8`) using `rw` + `rfl` — the learner never sees what the powerset actually contains

**What**: L05's proof is `rw [Finset.card_powerset]; rfl`. This is a two-tactic proof that bypasses any contact with the actual subsets. The learner proves the *size* of the powerset without ever proving membership in it. The conclusion lists all 8 subsets in a table, but the learner never verified any of them.

**Why**: The plan assigns coverage item E8 (concretization of powerset) to this level. A purely cardinality-based proof doesn't concretize the powerset — it demonstrates a formula. A stronger level would include a membership check, e.g., proving `{1, 3} ∈ ({1, 2, 3} : Finset Nat).powerset` as part of a conjunction. This would let the learner use `Finset.mem_powerset` (which is declared in `DefinitionDoc` but never used in a proof) and actually interact with the powerset as a collection of subsets. The cardinality part can remain as the second conjunct.

**Where**: L05 — add a membership conjunct (e.g., `{1, 3} ∈ ({1, 2, 3}).powerset`).

**Effort**: Medium (modify the statement and add proof/hints for the new conjunct).

**Recommend**: Yes.

---

### 10. `ring` is declared as `NewTactic` in L04 but is only used in the author's proof (via `by ring`), not in any hint's guided path — the learner may never learn what `ring` does

**What**: L04 declares `NewTactic ring` and includes a `TacticDoc ring` explaining it. But the proof uses `ring` only inside `exact ⟨_, by simp, by ring⟩` constructions (lines 66-70), which appear in the hidden backward-direction hint. The non-hidden hints guide the learner through `rcases` and `simp` without mentioning `ring`. A learner following the visible hints might never use `ring`.

**Why**: If `ring` is important enough to declare as `NewTactic` with a `TacticDoc`, it should be important enough that the guided proof path uses it in a visible way. Otherwise the declaration is noise. Either make `ring` visible in the hints (e.g., a hint saying "Each case like `1^2 = 1` can be closed by `ring`") or defer the `NewTactic ring` declaration to a level where `ring` is the primary tool.

**Where**: L04 — adjust hints to mention `ring` explicitly, or defer `NewTactic ring`.

**Effort**: Low (add a hint phrase).

**Recommend**: Consider.

---

## Overall impression

The FinsetExploration world delivers on its plan promise: the learner works concretely with {1, 2, 3, 4, 5} across filter, image, powerset, and product. The `ext`-and-simplify pattern appears repeatedly, which builds fluency. The conclusions are detailed, include helpful tables (the filter table in L03, the subset table in L05, the comparison table in L04), and consistently provide "in plain language" transfer statements. The boss (L07) is a genuine integration exercise that asks the learner to recall four different techniques.

The single most important improvement is **suggestion 9**: L05 proves the powerset has 8 elements but never asks the learner to interact with the powerset as a collection of subsets. Adding a membership conjunct (e.g., `{1, 3} ∈ ({1, 2, 3}).powerset`) would turn this from a formula-application level into a genuine concretization of powerset, fulfilling the plan's coverage item E8. The `Finset.mem_powerset` lemma is already documented in L05 but never used — this is a natural place to use it. The closely related suggestion 1 (missing `NewTactic refine` in the boss) and suggestion 3 (misplaced `NewTactic rintro`) are inventory hygiene issues that should also be addressed to avoid learner confusion.
