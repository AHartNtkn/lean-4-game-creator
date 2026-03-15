# W12_ps CountingPset — Enrichment Review (Round 2)

**Reviewer**: enrichment-reviewer
**Date**: 2026-03-15
**World**: CountingPset (W12_ps — Pset, 7 levels)
**Predecessor**: CountingPigeonhole (W12, 10 levels) + CountingFunctions (W12_ex, 5 levels)
**World promise**: The learner retrieves counting and pigeonhole skills under reduced scaffolding.
**Prior round**: R1 had 2 "Yes" items:
- R1-#3: L03 tested V16 (reverse-pigeonhole / no-surjection) instead of the planned V15 (subset → card inequality). **Fixed**: L03 redesigned to test V15 via `Finset.card_le_card`.
- R1-#1: L04 did not extract a witness — it was another `rw/omega` level. **Fixed**: L04 redesigned around `Finset.Nonempty`.

---

## Verification of R1 fixes

### R1-#3 (L03 — V15 retrieval): VERIFIED FIXED

L03 now presents `s ⊆ t` for abstract `Finset Nat` values and asks the learner to prove `s.card ≤ t.card`. The proof is `exact Finset.card_le_card h`, which is the correct V15 proof move as taught in W10 L06 (`FinsetInduction/L06_SubsetCardInequality.lean`). The level uses abstract finsets rather than concrete literals, which is a fresh surface form compared to the original W10 level (which used `{1,2} ⊆ {1,2,3}`). The conclusion correctly identifies this as V15 retrieval and provides a clear plain-language translation. **Fix is correct and complete.**

### R1-#1 (L04 — V8/V9 retrieval): PARTIALLY FIXED — SEE SUGGESTION #1

L04 now presents `h : s.Nonempty` and asks the learner to prove `∃ x, x ∈ s`. The introduction says to "Use `obtain` to extract the witness." However, `Finset.Nonempty s` is *defined* as `∃ x, x ∈ s`, so the goal is *definitionally equal to the hypothesis*. The proof is `exact h`. The hint even says this: "Use `exact h`. `Finset.Nonempty` is defined as `∃ x, x ∈ s`, so the hypothesis IS the goal." The conclusion acknowledges this and tries to redirect attention to the `obtain` lesson, but the level as written does not require `obtain` at all — `exact h` is the simplest and most natural proof. See suggestion #1.

---

## Ranked Suggestions

### 1. L04 still does not force V8 (witness extraction) — `exact h` closes it trivially

**What**: L04 asks the learner to prove `∃ x, x ∈ s` given `h : s.Nonempty`, but `Finset.Nonempty` is definitionally `∃ x, x ∈ s`, so `exact h` closes the goal without any witness extraction.

**Why**: This is the same fundamental issue as R1-#1, just in a different form. The R1 reviewer recommended making the goal require doing something *with* the witness — for example, given `s.Nonempty` and `∀ x ∈ s, P x`, prove `∃ x ∈ s, P x`. That formulation forces `obtain ⟨x, hx⟩ := h` followed by `exact ⟨x, hx, hP x hx⟩` (or similar), which genuinely retrieves V8. The current formulation retrieves nothing — the learner who tries `exact h` first (which any learner familiar with definitional equality will try) learns nothing about witness extraction.

The conclusion tries to save the level by saying "the lesson is not about this specific proof — it is about recognizing that nonemptiness gives you a witness" and suggesting the learner could use `obtain` in a larger proof. But a pset level should *test* a skill, not merely remind the learner that the skill exists. The conclusion even teaches `obtain ⟨x, hx⟩ := h` as an afterthought, which is the opposite of retrieval — the learner should already know this and demonstrate it, not be taught it in the conclusion.

**Where**: L04. Redesign the statement so the goal is not definitionally equal to any hypothesis. The R1 suggestion remains the best fix: given `(h : s.Nonempty)` and `(hP : ∀ x ∈ s, P x)`, prove `∃ x ∈ s, P x`. This forces the learner to destructure `h` with `obtain ⟨x, hx⟩ := h`, then apply `hP` to get `P x`, then repackage with `exact ⟨x, hx, hP x hx⟩`. This is a genuine V8 retrieval: the learner must extract a witness and *use* it.

**Effort**: Medium (modify level statement and proof).

**Recommend**: Yes — this is the same issue as R1-#1. The redesign did not fix the underlying problem. The goal must not be definitionally equal to the hypothesis.

---

### 2. L03 is a one-step proof (`exact Finset.card_le_card h`) with no proof structuring — it tests recall of a lemma name, not fluency with V15

**What**: L03's proof is `exact Finset.card_le_card h`. The learner needs to remember the lemma name and apply it. This is a knowledge-retrieval test (can you recall the name `Finset.card_le_card`?) rather than a proof-fluency test (can you use the subset-cardinality proof move in context?).

**Why**: In a pset world with reduced scaffolding, the purpose is to test whether the learner can *deploy* skills under less guidance. A one-step `exact` proof tests memory, not deployment. Compare with L02 (pigeonhole), which requires `apply ... ; rw [...] ; omega` — a three-step proof that tests the ability to set up pigeonhole, evaluate cardinalities, and close arithmetic. L03 is significantly simpler. A more demanding retrieval would embed the `card_le_card` step inside a larger argument — for example, "prove `s.card < t.card + 1` given `s ⊆ t`" (requires `card_le_card` followed by `omega`), or "given `s ⊆ t` and `t.card = 5`, prove `s.card ≤ 5`" (requires `card_le_card` followed by `linarith`/`omega`). These are still simple but exercise V15 as a proof *move* rather than as a lemma *recall*.

**Where**: L03. Enrich the statement to require at least one additional proof step beyond `exact Finset.card_le_card h`.

**Effort**: Low (add an arithmetic or rewriting step to the goal).

**Recommend**: Consider — the current level is a valid retrieval exercise, but it underperforms relative to the other levels' proof complexity.

---

### 3. R1-#4 (transfer framing) was not addressed — L05 and L06 introductions still do not prompt the learner to formulate the paper proof first

**What**: R1 suggestion #4 recommended adding a sentence to L05 and L06 introductions: "Before typing any Lean, write down the paper proof in your head (or on scratch paper). Then confirm it in Lean." This was marked "Yes" in R1. The current introductions do not contain any such prompt.

**Why**: Transfer levels are the pset world's unique contribution — they are the levels that test whether knowledge moves from Lean to paper mathematics. Without an explicit prompt to perform the transfer *before* the Lean proof, the learner may solve the Lean exercise mechanically and then read the transfer paragraph in the conclusion passively. The prompt costs one sentence and makes the transfer activity deliberate rather than incidental.

**Where**: L05 introduction (add before the "Recall:" or hint block) and L06 introduction (add before the hint block).

**Effort**: Low (one sentence per level).

**Recommend**: Yes — this was a "Yes" item in R1 that was not implemented.

---

### 4. The boss conclusion's retrieval table has inaccurate references

**What**: The boss conclusion contains a table:
```
| L03 | Reverse pigeonhole / no surjection (V15) | W12_ex |
```
But L03 was redesigned and now tests `Finset.card_le_card` (subset → card inequality), not "reverse pigeonhole / no surjection." The table still references the old L03 content. Additionally, V15 is "cardinality monotonicity from subset" in the plan, not "reverse pigeonhole / no surjection."

**Why**: An incorrect retrieval table misleads the learner about what they practiced and creates an internal inconsistency within the world. The table should accurately reflect the redesigned L03.

**Where**: L07 conclusion. Update the L03 row to read:
```
| L03 | Subset → card inequality (V15) | W10 |
```
(The skill was originally taught in W10 FinsetInduction L06, not W12_ex.)

**Effort**: Low (fix one table row).

**Recommend**: Yes — factual error in the world's own summary.

---

### 5. L04 conclusion claims retrieval of V9 but the level does not test V9 at all

**What**: The conclusion says: "The dual move (V9) is contradiction: if you know a type is nonempty but also that its cardinality is 0, you have a contradiction." But V9 (contradiction via cardinality) is not tested anywhere in this level — or in the world at all. V9 was taught in W12 L05 via `Finset.card_eq_zero` and `Finset.notMem_empty`. No level in CountingPset retrieves this proof move.

**Why**: The plan says L04 should retrieve V8 *and* V9. Even if L04 is fixed to properly retrieve V8 (suggestion #1), V9 remains untested. Mentioning it in a conclusion is not retrieval — the learner reads about it but never practices it. If V9 is a genuine retrieval target for this pset world, it needs a level (or a component of a level) that requires the learner to derive a contradiction from `s.card = 0` and `x ∈ s`.

**Where**: Two options:
- **Option A (preferred)**: Fold a V9 step into the redesigned L04. For example: given `s.Nonempty`, `∀ x ∈ s, P x`, and `t.card = 0` where `t = s.filter (fun x => ¬P x)`, prove `∀ x ∈ s, P x` by contradiction using `card_eq_zero`. This is complex; simpler alternatives exist.
- **Option B**: Add a brief L04b or modify the boss to include a `card_eq_zero`-based contradiction step. For example, in the boss, add a hypothesis that forces the learner to rule out an empty case before applying pigeonhole.
- **Option C**: Accept that V9 is not retrieved in this world and remove the V9 tag from the conclusion. The plan lists V8 (T) and V9 (T) for L04, but if V9 is genuinely hard to test without adding a level, explicitly acknowledge this as deferred.

**Effort**: Medium to high depending on option.

**Recommend**: Consider — V9 coverage is a genuine gap, but the fix is not obvious. At minimum, remove the misleading V9 mention from L04's conclusion.

---

### 6. Every level except L03 and L04 follows the `apply/rw/omega` proof template — R1-#2 identified this and it is only partially addressed

**What**: L01 is `rw; rw; (implicit norm_num)`. L02 is `apply; rw; omega`. L05 is `apply; rw; omega`. L06 is `rw; rw; norm_num`. L07 is `apply; rw; omega`. L03 is now `exact ...` and L04 is `exact h`. So five of seven levels use the identical `rw/omega` template, one is a single `exact`, and one is a trivial identity. The world's proof-shape diversity is low.

**Why**: R1-#2 was marked "Yes" — the world should test retrieval of distinct proof moves, not repeated application of the same template. The redesigned L03 and L04 were supposed to break the monotony, but L03 is a single `exact` (even less proof structuring than `rw/omega`) and L04 is `exact h` (zero proof structuring). The world would benefit from at least one level requiring `intro`, `have`, `obtain`, or a case split.

**Where**: The fix to suggestion #1 (redesigning L04 to require `obtain` + usage of the witness) would partially address this by introducing a genuinely different proof shape. No additional changes needed beyond fixing L04.

**Effort**: N/A (addressed by suggestion #1).

**Recommend**: No separate action needed — implementing suggestion #1 resolves this.

---

### 7. L01 introduction says "Recall:" with specific lemma names, which provides more scaffolding than a pset level should

**What**: L01's introduction lists three specific lemma names: `Fintype.card_prod`, `Fintype.card_fin`, `Fintype.card_bool`. This is the same level of scaffolding as a lecture level. The pset world's stated purpose is "reduced scaffolding: fewer hints, fresh surface forms, and no new theorems."

**Why**: Providing the exact lemma names in the introduction means the learner does not need to recall them from memory. The "retrieval" becomes "read the introduction, type the listed lemmas." For a pset level, the introduction should describe the *task* and possibly hint at the *strategy* (e.g., "decompose the product, then evaluate each factor"), but providing exact lemma names undermines the retrieval challenge.

**Where**: L01, L02 introductions. Replace explicit lemma names with strategy descriptions. For example, L01 could say "Recall the strategy: decompose the product type, then evaluate the cardinality of each factor." The learner must then recall `Fintype.card_prod`, `Fintype.card_fin`, and `Fintype.card_bool` from their inventory.

**Effort**: Low (rewrite 2-3 sentences per level).

**Recommend**: Consider — there is a tension between reduced scaffolding and learner frustration. The hidden hints already provide the lemma names as a fallback. Removing them from the introduction would make the introduction-level scaffolding genuinely "reduced" while keeping the hint-level scaffolding available.

---

### 8. L06 comparison table references levels from W12 and W12_ex but uses level numbers (not world-qualified identifiers) that could confuse the learner

**What**: The L06 conclusion contains:
```
| `Fin 2 → Fin 3` | 9 | $3^2$ |
| `Fin 3 → Bool` | 8 | $2^3$ |
| `Fin 4 → Fin 3` | 81 | $3^4$ |
```
These computations were performed in W12 L02, W12_ex L04, and this level (W12_ps L06), respectively. The table does not say which world each came from. In a course with 24+ worlds, a learner revisiting this level may not remember where they first saw `Fin 2 → Fin 3`.

**Where**: L06 conclusion. Add a column or parenthetical noting the world of origin.

**Effort**: Low (add parentheticals).

**Recommend**: Consider — this is a minor clarity improvement.

---

## Overall Impression

The R1 fix for L03 is correct and effective: the level now retrieves V15 (subset → card inequality via `Finset.card_le_card`) on a genuinely fresh surface form. The R1 fix for L04 is well-intentioned but does not solve the underlying problem: the goal is still definitionally equal to the hypothesis, making `exact h` the natural proof and `obtain` an unnecessary detour.

The world's strengths are real: clean writing, consistent disabled-tactic baseline, good transfer paragraphs in L05 and L06, a well-structured boss that integrates counting and pigeonhole, and a useful retrieval table in the boss conclusion. The level ladder (fresh counting → fresh pigeonhole → subset inequality → nonemptiness → transfer × 2 → boss) covers the plan's seven retrieval targets.

**The single most important improvement** is redesigning L04 so that the goal cannot be closed by `exact h`. The fix is straightforward: make the goal require the learner to *use* the extracted witness (e.g., combine `s.Nonempty` with a universally quantified hypothesis). This was the R1 reviewer's original recommendation and it remains the right one. Once L04 genuinely forces `obtain`, the world will have a level with a different proof shape from the `rw/omega` template, and V8 will be honestly retrieved.
