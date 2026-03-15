# W9 FinsetCardinality — Enrichment Review (Round 2)

## R1 correction log

Before new analysis, two R1 claims were flagged by the coordinator as incorrect. Verification:

| R1 claim | Verdict | Evidence |
|----------|---------|----------|
| "`omega` is undeclared — add `NewTactic omega`" | **FALSE.** `omega` is declared as `NewTactic` in W1 FinIntro L01 (`finite_math/Game/Levels/FinIntro/L01_WhatIsFin.lean`, line 121: `NewTactic omega exact intro «have» assumption apply rw constructor use cases`). Once declared anywhere in the game, a tactic is globally available. No action needed. | File verified. |
| "Boss doesn't test inclusion-exclusion" | **FALSE.** L09 Boss Part 2 is `exact Finset.card_union_add_card_inter _ _`, which is the inclusion-exclusion lemma. The boss does test it. | L09 lines 46-49 verified. |

Both corrections are confirmed. These items are closed.

---

## Ranked suggestions (R2)

### 1. `simp` is missing from DisabledTactic across all 9 levels

**What**: The DisabledTactic line in every level is `trivial decide native_decide aesop simp_all`, but `simp` is absent. The established standard set (per project memory) is `trivial decide native_decide simp aesop simp_all`.

**Why**: `simp` with its default lemma set can close many of the goals in this world. For example, `simp` can close `(∅ : Finset Nat).card = 0` (L01), `({42} : Finset Nat).card = 1` (L02), `(Finset.range 5).card = 5` (L05), `Finset.range 0 = ∅` (L06 part 1), and `(Finset.range 0).card = 0` (L06 part 2). With `simp` enabled, a learner can bypass the intended lemma-application exercise by typing `simp` on nearly every level. This defeats the world's purpose of teaching specific cardinality lemmas one at a time.

**Where**: All 9 level files — add `simp` to each DisabledTactic line.

**Effort**: Low (mechanical edit to 9 lines).

**Recommend**: Yes.

---

### 2. Every non-boss level is a one-liner `exact`/`rw` — no level requires multi-step reasoning

**What**: L01 through L08 are each solved by a single tactic application (`rw [lemma]` or `exact lemma args`). The only level requiring more than one step is L06, which has a `constructor` followed by two one-liners. The boss (L09) uses `refine` to split into three goals, each closed by a single `exact`.

**Why**: The world teaches 6 new lemmas (card_empty, card_insert_of_mem, card_range, range_zero, card_union_add_card_inter, card_filter_le) plus retrieves 2 from prior worlds (card_singleton, card_insert_of_notMem). But the learner never *combines* these lemmas in a single proof. A level requiring multi-step cardinality reasoning — such as computing `({1, 2, 3} : Finset Nat).card = 3` by peeling off `card_insert_of_notMem` twice then using `card_singleton` — would exercise the "insertion peeling" strategy described in L03's conclusion ("Peel off each `insert` using `card_insert_of_notMem`. Handle the innermost singleton with `card_singleton`."). That strategy is described but never practiced. The boss avoids this because each of its three parts is a single-lemma application.

**Where**: A new level between L04 and L05 (after both insert lemmas are taught), or modify L04 to include a multi-step second part.

**Effort**: High (new level) or medium (modify L04).

**Recommend**: Yes.

---

### 3. The "insertion peeling" strategy is described in L03 but never named or practiced

**What**: L03's conclusion describes a three-step pattern: (1) peel off each `insert` using `card_insert_of_notMem`, (2) handle the innermost singleton with `card_singleton`, (3) let arithmetic close the remaining goal. This is described under "The pattern" but is never given a memorable name, and no level requires the learner to execute it.

**Why**: This is a genuine proof strategy that will appear in W10 (Finset induction). Naming it ("the **peeling strategy**" or "**insertion peeling**") would make it referenceable in later worlds. More importantly, having a level that requires the learner to actually *execute* the three-step pattern would move it from "read about" to "practiced." This ties directly to suggestion #2: the multi-step level would be where this strategy is first practiced.

**Where**: L03 conclusion (name the strategy), and the new level from suggestion #2 (practice it).

**Effort**: Low (naming) + High (tied to suggestion #2's new level).

**Recommend**: Yes.

---

### 4. L07 inclusion-exclusion: no numerical verification step — the identity is applied but not checked

**What**: L07 asks the learner to prove inclusion-exclusion for `{1,2,3}` and `{2,3,4}` by applying `Finset.card_union_add_card_inter`. The conclusion then *tells* the learner what the numbers are (4 + 2 = 3 + 3), but the learner never verifies this. The proof is a single `exact`.

**Why**: The whole point of using concrete finsets is to ground the abstract identity in actual numbers. But the learner never sees the numbers — they apply the general lemma and move on. A stronger exercise would have a second part that asks the learner to verify the numerical instance, e.g., prove `(({1, 2, 3} : Finset Nat) ∪ {2, 3, 4}).card = 4` (which would require `simp` or `decide` — or alternatively, use the peeling strategy). Alternatively, the exercise could state inclusion-exclusion in its *subtractive* form `(s ∪ t).card = s.card + t.card - (s ∩ t).card` and require the learner to derive it from the additive form plus `omega`, which would exercise the transfer between the two formulations mentioned in the introduction.

**Where**: L07 — add a second conjunct, or modify the statement.

**Effort**: Medium.

**Recommend**: Consider.

---

### 5. L01 re-introduces `card_singleton` and `card_insert_of_notMem` as known but no retrieval gate verifies the learner can still use them

**What**: L01's conclusion lists three cardinality lemmas (card_empty, card_singleton, card_insert_of_notMem) and says "Together, these three lemmas let you compute the cardinality of any finset built by iterated `insert`." L02 is a retrieval exercise for card_singleton and L03 for card_insert_of_notMem, but both are single-step applications.

**Why**: These retrieval exercises are appropriate but are so trivially structured (each is one `rw` or `exact` away from done) that they don't actually test whether the learner can *find* the right lemma. The learner sees the lemma name in the introduction text and applies it. A retrieval exercise that withholds the name in the introduction and asks the learner to recall it from memory would be a stronger test. L02's introduction explicitly says "Recall: `Finset.card_singleton a : ({a} : Finset α).card = 1`" — so the "retrieval" is actually "copy from the text above." This is a minor point but worth noting: true retrieval means the learner must access memory, not just read the current screen.

**Where**: L02 and L03 introductions — remove or reduce the explicit lemma statement. Let the Hint system provide it if needed, but make the introduction focus on *what the goal looks like* rather than *which lemma to use*.

**Effort**: Low (text edits).

**Recommend**: Consider.

---

### 6. The subtractive form of inclusion-exclusion is mentioned but never derived — a missed "derivable result" moment

**What**: L07's introduction and conclusion both mention the subtractive form `|A ∪ B| = |A| + |B| - |A ∩ B|` and note that the additive form avoids Nat subtraction. But the relationship between the two forms is never made explicit in a proof.

**Why**: The derivation of one from the other is a one-line `omega` step (given the additive form, `omega` produces the subtractive form or vice versa). This is a "derivable result presented as a fact" — exactly the kind of enrichment opportunity the reviewer should flag. A level or a bonus part asking the learner to derive `(s ∪ t).card = s.card + t.card - (s ∩ t).card` from `card_union_add_card_inter` using `omega` would make the connection active rather than passive. However, this requires Nat subtraction, which has well-known pitfalls (truncation at 0). The level could also serve as a brief encounter with Nat subtraction hazards, foreshadowing later worlds.

**Where**: New sub-part in L07, or a separate short level between L07 and L08.

**Effort**: Medium (if new level) or Low (if added as part 2 of L07).

**Recommend**: Consider.

---

### 7. The boss conclusion's "What you learned" table uses level numbers (L01-L09) without world context

**What**: The boss conclusion contains a table mapping concepts to "L01" through "L09". These numbers are internal to this world, not global. But in the game UI, the learner may see them differently.

**Why**: This is a minor usability point. The level numbers L01-L09 within the world are fine if the game UI displays them that way. If the game UI uses different numbering or just shows level titles, these references would be confusing. The table is otherwise excellent — it provides a clean summary of the world's scope. This is low-priority but worth flagging.

**Where**: L09 conclusion.

**Effort**: Low (verify that game UI uses same numbering; if not, use level titles instead).

**Recommend**: Consider.

---

### 8. No level explores what happens when the `card_insert_of_notMem` hypothesis fails — a "what if?" missed opportunity

**What**: L03 teaches `card_insert_of_notMem` (inserting a new element) and L04 teaches `card_insert_of_mem` (inserting a duplicate). But there is no level that forces the learner to *determine* which case they are in and apply the correct lemma. The two cases are taught in isolation.

**Why**: In real proofs, the learner will face `(insert a s).card` without knowing whether `a ∈ s`. They will need to case-split on membership (or use `Decidable.em` / `by_cases`). A level asking "given `s` and `a` with no membership hypothesis, prove that `(insert a s).card ≤ s.card + 1`" (which is `Finset.card_insert_le`) would force the learner to think about both cases and use the bound that holds regardless. This is a natural next step after L03-L04 and would preview the proof move of case-splitting on membership.

**Where**: New level between L04 and L05.

**Effort**: High (new level with new lemma).

**Recommend**: Consider.

---

## Overall impression

The world has a clean, well-ordered structure: base case (L01), singleton retrieval (L02), insert-new (L03), insert-duplicate (L04), range (L05-L06), inclusion-exclusion (L07), filter bound (L08), boss integration (L09). The introductions are consistently well-written, the transfer moments are genuine, and the conclusion tables are excellent pedagogical devices. The world correctly addresses misconception C9 (0-indexing of range) and provides good foreshadowing for W10 (Finset induction).

The single most important improvement is **adding `simp` to DisabledTactic** (suggestion #1) — without this, the majority of levels can be bypassed. The second most important improvement is **adding a multi-step level that practices the insertion-peeling strategy** (suggestion #2). Currently every level in the world is a one-step proof, and the one genuine proof strategy the world introduces (peel inserts, then use card_singleton, then arithmetic) is described in text but never exercised. These two changes together would significantly strengthen the world's educational value.
