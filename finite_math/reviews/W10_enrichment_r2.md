# W10 FinsetInduction — Enrichment Review (Round 2)

## R1 fix verification

**Fix 1: `insert_union` introduced as `NewTheorem` in L05 with `TheoremDoc`.**
Verified. L05_CardInsertLe.lean lines 88-95 now contain a `TheoremDoc` for `Finset.insert_union` and `NewTheorem Finset.insert_union`. This removes the lottery-move concern from L09 (boss): the learner now has `insert_union` in their inventory before the boss level. Fix is correct and complete.

**Fix 2: `Nat.succ_eq_add_one` flagged as R1 reviewer error.**
Verified. No level in the world uses or requires `Nat.succ_eq_add_one`. The R1 reviewer was incorrect in flagging this. No action needed.

**Outstanding from R1:** The R1 review raised 10 suggestions. Only fixes for the `insert_union` lottery move were implemented. The remaining R1 suggestions are re-evaluated below against the current state of the world.

---

## Ranked suggestions

### 1. The stale file `L05_CardinalityByInduction.lean` is still present and not imported

**What**: The file `L05_CardinalityByInduction.lean` exists in the directory but is not imported by `FinsetInduction.lean`. It contains a duplicate Level 5 declaration (the same level number as the active `L05_CardInsertLe.lean`).

**Why**: This is a maintenance hazard. Two files claim to be Level 5, but only one is imported. Anyone looking at the directory sees 10 `.lean` files and expects 10 levels, but the world only has 9. The stale file could be accidentally imported, causing a build error (duplicate level 5). More substantively, the stale file's content — proving `s = ∅ → s.card = 0` as the converse of L03 — has genuine pedagogical value. R1 suggestion #8 flagged this and recommended either integrating or deleting. It remains unresolved.

**Where**: Delete `L05_CardinalityByInduction.lean`, or integrate its content into the world (e.g., as a level between L03 and L04 that completes the `card_eq_zero` iff).

**Effort**: Low (delete) to medium (integrate as a new level).

**Recommend**: Yes. At minimum, delete. Ideally, integrate — the "both directions of an iff" pattern is valuable pedagogy and introduces `Finset.insert_ne_empty`, which is currently only taught in the un-imported stale file.

---

### 2. `simp` is not disabled in 8 of the 9 levels

**What**: Only L07 disables `simp`. All other levels (L01-L06, L08-L09) disable `trivial decide native_decide aesop simp_all` but not `simp`. The project's standard disabled set (from project memory) is `trivial decide native_decide simp aesop simp_all`.

**Why**: `simp` can partially or fully solve goals in several levels. For example, in L02 the insert case goal `insert a s' = ∅ ∨ (insert a s').Nonempty` can be closed by `simp`. In L03, the base case `(∅ : Finset α).card = 0` simplifies by `simp [Finset.card_empty]`. In the boss (L09), `simp [Finset.empty_union]` can handle the base case. This undermines the intended learning where the student should apply specific lemmas. The inconsistency with L07 (which does disable `simp`) confirms this is an oversight, not a deliberate choice.

**Where**: Add `simp` to the `DisabledTactic` line in L01, L02, L03, L04, L05, L06, L08, L09.

**Effort**: Low (add one word to 8 lines).

**Recommend**: Yes.

---

### 3. L06 is a one-step `exact` application — the learner never practices finset induction with a subset-cardinality argument

**What**: L06 gives the learner a subset hypothesis `h : {1, 2} ⊆ {1, 2, 3}` and asks them to prove `{1, 2}.card ≤ {1, 2, 3}.card`. The entire proof is `exact Finset.card_le_card h`. The conclusion mentions that `card_le_card` is internally proved by finset induction, but the learner never sees or reproduces this argument.

**Why**: This was R1 suggestion #2 (rated "Yes"). Between L04 (which teaches the insert step mechanics) and L09 (which demands a full induction proof combining `insert_union`, `card_insert_le`, `card_insert_of_notMem`, and `ih` with `omega`), the learner needs at least one level where they perform a complete finset induction that meaningfully uses `ih` in an arithmetic subgoal. L05 (the active version) is a `by_cases` proof, not induction. L06 is a one-step application. L07 is Nat induction. L08 is about `refine` style. The gap remains: no level between L04 and L09 exercises the full "decompose-compute-reassemble" pattern with `ih`.

The current L06 is fine as a quick "here is the tool" level, but it should not be the only exposure to subset-cardinality reasoning before the boss. Consider either (a) making L06 a guided finset induction proof of `card_le_card` (disabling the library lemma and walking the learner through the induction), or (b) adding a new level after L06 that proves a cardinality result by induction where `ih` is needed for the arithmetic closure.

**Where**: L06, or a new level between L06 and L07.

**Effort**: High (rewriting a level or adding one).

**Recommend**: Yes. This is the world's structural gap, identified in R1 and still present.

---

### 4. The "decompose-compute-reassemble" strategy pattern is never named

**What**: The insert case across L03, L04, L05, L07, L08, and L09 follows the same three-step shape: (1) decompose `insert a s'` using a lemma, (2) compute/bound using `ha` and `ih`, (3) close with `omega`. This pattern is used six times but never named.

**Why**: R1 suggestion #3 (rated "Yes"). Naming proof strategies aids transfer. When the learner encounters `Finset.sum_insert` or `Finset.prod_insert` in W13-W14, recognizing the same shape will accelerate learning. One sentence in a conclusion (L04 or L05) would make this implicit knowledge explicit: "The insert step in finset induction almost always follows a decompose-compute-reassemble pattern: rewrite the operation on `insert a s` using a decomposition lemma, simplify using `ha` and `ih`, then close the arithmetic."

**Where**: L04 or L05 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Yes.

---

### 5. L09 conclusion does not foreshadow big-operator induction (W13-W14)

**What**: L09's conclusion mentions "the next world is the Finset Reasoning problem set" but says nothing about how the finset induction principle taught here underpins `sum_insert`, `sum_cons`, and inductive sum proofs in W13-W14.

**Why**: R1 suggestion #7 (rated "Yes"). This is the most natural foreshadowing opportunity. A single sentence like "The `Finset.induction_on` principle you learned here is exactly how the big-operator library decomposes `Finset.sum` and `Finset.prod` over finsets. When you reach the big-operator worlds, you will see this decompose-compute-reassemble pattern again with sums instead of cardinalities" costs nothing and creates a forward link. The plan confirms W13 depends directly on W10, so this connection is architecturally real.

**Where**: L09 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Yes.

---

### 6. L01 disables `omega` but L03-L09 do not — `omega` can shortcut the base case in L03 and L04

**What**: L01 disables `omega` (along with the standard set). L03 through L09 all use `omega` as part of the intended proof but do not disable it. This is intentional — `omega` is a tool in this world. However, in L03 the base case `∅.card = 0 → ∅ = ∅` can be closed by the intended `rfl`, but the implication `(∅ : Finset α).card = 0 → (∅ : Finset α) = ∅` is vacuously handled by `omega` if the types align. More importantly, L02's base case `∅ = ∅ ∨ (∅ : Finset α).Nonempty` and L04's base case with `absurd` cannot be solved by `omega` (they are about propositions, not arithmetic), so the risk is limited.

**Why**: This is a minor point. `omega` is intentionally part of the world's toolkit from L03 onward. The levels where `omega` closes goals are levels where it is the intended closer (L03 insert case, L04 insert case, L05, L07, L08, L09). The base cases that should not be `omega`-closed are about propositions, not arithmetic. No action needed.

**Where**: N/A.

**Effort**: N/A.

**Recommend**: No action needed. Noted for completeness.

---

### 7. L02's first finset induction proof does not use `ih` — this is pedagogically intentional but could be noted more explicitly

**What**: R1 suggestion #5 noted that L02 proves `s = ∅ ∨ s.Nonempty`, which does not use the inductive hypothesis. The conclusion already notes "we did not even need `ih`", which is good. R1 suggested replacing L02 with an example that uses `ih`.

**Why**: On reflection, the current L02 is well-designed. The learner is learning the *syntax* of `Finset.induction_on` for the first time. Having the first example be syntactically straightforward — even if `ih` is not used — lets the learner focus on the mechanics of `case empty` / `case insert` without also juggling an arithmetic step. L03 immediately follows with a proof that uses `ih`. The progression from "here is the syntax" (L02) to "now use the inductive hypothesis" (L03) is sound pedagogy. The existing conclusion note ("we did not even need `ih` — in harder proofs, the inductive hypothesis will be essential") is exactly the right framing.

**Where**: N/A.

**Effort**: N/A.

**Recommend**: No change needed. R1 suggestion #5 is appropriately declined — the current design is pedagogically intentional and well-signposted.

---

### 8. L05 (`CardInsertLe`) introduces `by_cases` as a proof strategy but does not add it as `NewTactic`

**What**: L05 teaches the learner to use `by_cases h : a ∈ s` as a proof strategy. The introduction explains the pattern and the proof relies on it. However, `by_cases` is not declared as `NewTactic` in L05. If `by_cases` was introduced in a previous world, this is fine. If L05 is the first time the learner encounters `by_cases`, it should be declared.

**Why**: The game engine uses `NewTactic` declarations to populate the tactic panel. If `by_cases` was not previously declared, the learner will not see it in their tactic inventory, making it harder to discover. This is a consistency issue rather than a gap — the learner is told to use `by_cases` in the hints, so they will use it regardless. But proper inventory management is part of the world author's responsibility.

**Where**: L05, add `NewTactic by_cases` if not introduced in an earlier world (W5-W9).

**Effort**: Low (one line).

**Recommend**: Consider. Depends on whether `by_cases` was already declared in W5-W9.

---

### 9. No concrete counterexample shows what happens when `a ∈ s` in the insert step

**What**: R1 suggestion #10 (rated "Consider"). L04 explains why `ha : a ∉ s` matters but never shows a concrete case where `a ∈ s` and `insert a s = s`, so `card (insert a s) = card s` (no change). A quick worked example would ground the abstract explanation.

**Why**: This is a "what if?" moment that would strengthen L04. One sentence in the conclusion: "For comparison, if we tried to insert 2 into {1, 2, 3}, we would get {1, 2, 3} again — the cardinality would not change. The hypothesis `a ∉ s` rules out this degenerate case." This makes the non-membership condition visceral rather than abstract.

**Where**: L04 conclusion.

**Effort**: Low (two sentences).

**Recommend**: Consider.

---

## Overall impression

The world has a strong architectural skeleton with a clear progression from Nat induction review (L01) through Finset induction introduction (L02-L04), proof strategies (L05 `by_cases`, L07 comparison, L08 `refine`), a library tool (L06 `card_le_card`), and a well-designed integration boss (L09). The R1 fix for `insert_union` is correctly implemented: the boss no longer requires a lottery move. The introductions and conclusions are well-written with good "in plain language" transfer moments and comparison tables.

**The single most important improvement** remains the structural gap between L04 and L09: there is no level where the learner performs a complete finset induction proof that meaningfully uses `ih` in an arithmetic subgoal on a simpler problem than the boss. L05 is `by_cases`, L06 is one-step `exact`, L07 is Nat induction, L08 is `refine` style. The boss demands all these skills combined, but the full "induction with cardinality and `ih`" pattern has not been practiced on a simpler target. Addressing suggestion #3 (rewriting L06 into a guided induction proof of `card_le_card`, or adding a level) would close this gap. The secondary priorities are cleaning up the stale file (#1) and adding `simp` to the disabled tactics (#2) — both are low-effort fixes that should be done regardless.
