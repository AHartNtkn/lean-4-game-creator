# W12 CountingPigeonhole -- Enrichment Review (Round 2)

**Reviewer**: enrichment-reviewer
**Date**: 2026-03-15
**World**: W12 CountingPigeonhole (Lecture, 10 levels)
**World promise**: The learner can count elements of compound finite types and apply the pigeonhole principle.
**Prior round**: R1 (two items noted by coordinator as resolved -- see notes at bottom)

---

## Ranked suggestions

### 1. L02 `Fintype.card_fun` is not actually a mathlib lemma name -- verify API correctness

**What**: L02 introduces and teaches `Fintype.card_fun` as a `NewTheorem` and `TheoremDoc` entry. However, the standard mathlib lemma for function-type cardinality is `Fintype.card_pi` (for dependent functions) or `Fintype.card_fun` may be a custom alias. If `Fintype.card_fun` is not a real mathlib name, the `TheoremDoc` is misleading and the learner's inventory will reference a non-existent lemma.

**Why**: If the lemma name is incorrect, the proof will not compile (or compiles only because a local alias was defined). The learner who tries to use `Fintype.card_fun` in a later world or outside this game will find it does not exist. This would be a factual error in the API documentation. If it does compile, it may be because mathlib does provide this name -- but this should be verified.

**Where**: L02 -- verify that `Fintype.card_fun` is the correct mathlib name. If not, replace with the correct name (likely `Fintype.card_pi` with the appropriate specialization, or `Fintype.card_fun`).

**Effort**: Low (verification + possible rename).

**Recommend**: Yes.

---

### 2. L04 and L05 use `Finset.card` / `Finset.Nonempty` but the world otherwise operates entirely in `Fintype.card` -- the transition is unexplained

**What**: L01-L03 and L06-L10 work with `Fintype.card` (type-level cardinality). L04 and L05 abruptly switch to `Finset.card` and `Finset.Nonempty` (finset-level operations). L04 works with `Finset Nat` (a finset of natural numbers) and L05 works with `Finset.card_eq_zero`. The relationship between `Fintype.card` and `Finset.card` is never explained, and the learner may be confused about why the API suddenly changed.

**Why**: The learner has been working with `Fintype.card (Fin n)` as a type-level counting concept. Suddenly in L04, the focus shifts to `Finset Nat` and `.Nonempty`, which is a different layer of the API. The bridge between these (`Fintype.card alpha = (Finset.univ : Finset alpha).card`, taught in W11 L03) is never referenced. A sentence in L04's introduction explaining "We now temporarily work with finsets directly, using skills from earlier worlds, to build proof moves we will need for pigeonhole" would smooth this transition.

**Where**: L04 introduction -- add a transitional paragraph.

**Effort**: Low (one paragraph).

**Recommend**: Yes.

---

### 3. L06 and L07 prove pigeonhole in two steps (specific then general), but the specific case (L06) is pedagogically redundant

**What**: L06 proves `not Injective f` for `f : Fin 4 -> Fin 3`. L07 proves the same for `f : Fin (n+1) -> Fin n`. The proof structure is identical in both levels: `intro hinj`, `have h := Fintype.card_le_of_injective f hinj`, `rw [Fintype.card_fin, Fintype.card_fin] at h`, `omega`. The only difference is concrete numbers vs. a variable `n`.

**Why**: Having a specific case before the general case is a valid pedagogical choice (concreteness fading). But when the proof is *identical* -- the same four steps, the same lemma names, the same closing tactic -- the specific case provides no additional insight. The learner learns nothing from L06 that L07 does not also teach. A better design for L06 would be to use a *different* proof strategy for the specific case (e.g., `fin_cases` + exhaustion, or a direct argument), so the learner sees two proof strategies and understands why the cardinality-based approach scales. However, `fin_cases` may be too expensive for `Fin 4 -> Fin 3` (it would require checking all 81 function pairs). Given this constraint, L06 serves as a "warm-up with concrete numbers" which is defensible. The real improvement would be to add a sentence in L07's conclusion acknowledging this: "Notice the proof was identical to L06 -- the same structure works for any `n`. This is a hallmark of good formal reasoning." -- which the conclusion already does (the table comparing L06 and L07). So the current design is actually well-handled.

**Where**: No change needed. The conclusion of L07 already addresses this.

**Effort**: N/A.

**Recommend**: No action needed. Withdrawing this suggestion.

---

### 4. L08 introduces `Fintype.exists_ne_map_eq_of_card_lt` but the relationship to L07's `pigeonhole` theorem is never articulated

**What**: L07 proves a theorem named `pigeonhole` and says "This statement has been added to your theorem inventory as `pigeonhole`." L08 then introduces a completely different lemma, `Fintype.exists_ne_map_eq_of_card_lt`, which is the "collision form" of pigeonhole. The relationship between these two formulations is mentioned in L08's conclusion table, but the introduction never explains *why* we need a different formulation. The learner might wonder: "I just proved `pigeonhole`. Why can't I use it here?"

**Why**: The learner proved `pigeonhole` (non-injectivity form) in L07 and was told it was added to their inventory. In L08, they are asked to prove something that looks like a consequence of pigeonhole, but they are told to use a *different* mathlib lemma instead of their own theorem. This creates a disconnect. The introduction should explain: "Your `pigeonhole` theorem proves non-injectivity. But sometimes you need the *witnesses* -- the actual colliding pair. Mathlib provides `Fintype.exists_ne_map_eq_of_card_lt` which gives you `exists x y, x != y and f x = f y`. This is strictly stronger."

**Where**: L08 introduction -- add 2-3 sentences explaining the relationship between the two forms and why the collision form is more useful in practice.

**Effort**: Low (a few sentences in the introduction).

**Recommend**: Yes.

---

### 5. The `pigeonhole` theorem from L07 is never used again in the world

**What**: L07 names its statement `pigeonhole` and the conclusion says it is added to the inventory. But L08, L09, and L10 all use `Fintype.exists_ne_map_eq_of_card_lt` (the collision form) instead. The learner's own theorem `pigeonhole` is never applied anywhere.

**Why**: Naming a theorem and telling the learner it is in their inventory creates an expectation that they will use it. If it is never used, the naming feels hollow. Two possible fixes: (a) add a level between L07 and L08 where the learner applies their `pigeonhole` theorem to a specific case (e.g., proving `not Injective f` for a specific `f : Fin 6 -> Fin 5` using `apply pigeonhole`), or (b) restructure L08 so the learner first uses `pigeonhole` to get non-injectivity, then is shown how the collision form provides more. Option (b) is more instructive but harder to implement. Option (a) is simpler but adds a level.

**Where**: L07 conclusion (soften the "added to inventory" language) or add a usage level.

**Effort**: Low if softening text; High if adding a level.

**Recommend**: Consider. At minimum, soften the L07 conclusion to say "This theorem captures the non-injectivity formulation. In the next level, you will see a stronger formulation that gives you the actual colliding pair."

---

### 6. `simp` is not in the `DisabledTactic` list -- potential exploit

**What**: Every level disables `trivial decide native_decide aesop simp_all` but does not disable `simp`. The project memory records that the standard disabled set should include `simp`.

**Why**: `simp` can close many of the cardinality goals in this world. For L01, `simp` closes `Fintype.card (Fin 2 + Fin 3) = 5`. For L02, `simp` likely closes `Fintype.card (Fin 2 -> Fin 3) = 9`. For L03, `simp` closes `Fintype.card (Option (Fin 3)) = 4`. If `simp` is available, the learner can bypass the named lemma workflow that is the entire pedagogical point of L01-L03. The L05 contradiction goal may also be closable by `simp` with the right lemmas.

**Where**: All 10 levels -- add `simp` to every `DisabledTactic` line.

**Effort**: Low (add one word per level).

**Recommend**: Yes.

---

### 7. No `NewTheorem` / `TheoremDoc` for `Fintype.card_fin` in this world, despite heavy reliance on it

**What**: `Fintype.card_fin` is used in L01, L02, L03, L06, L07, L08, L09, and L10 -- it appears in virtually every level. But it is never declared via `NewTheorem` in this world. If W11 already declared it, it may be available. But if the learner skipped W11 or if W11's declaration was missed (W11 R1 flagged this exact issue), then `Fintype.card_fin` is absent from the inventory despite being the world's most-used lemma.

**Why**: The learner who forgets the exact name has no inventory entry to consult. This was flagged as the #1 issue in W11's enrichment R1. If W11 was fixed to include it, this world inherits it. If not, this world should declare it itself.

**Where**: L01 (the first level that uses it). Add `NewTheorem Fintype.card_fin` and `TheoremDoc` if not already declared in a prerequisite world.

**Effort**: Low (check W11, add if missing).

**Recommend**: Yes.

---

### 8. L09 is nearly identical to L08 in proof structure -- the "transfer" claim is not substantiated by the level design

**What**: L09 is titled "Six people, five rooms" and its introduction says "This is the **transfer moment**: can you recognize pigeonhole in a word problem and apply the same formal tool?" But the proof is identical to L08: `apply Fintype.exists_ne_map_eq_of_card_lt`, `rw [Fintype.card_fin, Fintype.card_fin]`, `omega`. The variable names change from `f` to `assign`, and the numbers change from 5/4 to 6/5, but the proof structure is identical.

**Why**: True transfer requires the learner to do something *different* with the knowledge -- applying it in a new context where the mapping from problem to formalism is nontrivial. Here, the problem is already fully formalized (`assign : Fin 6 -> Fin 5`), so there is no recognition step. The learner never has to model the problem; they just apply the same lemma to different numbers. The transfer claim in the introduction is aspirational but the level does not deliver on it. A genuine transfer level would present the problem in natural language and require the learner to *choose* the formalization (e.g., providing the function type as part of the goal, or asking the learner to state the pigeonhole application before proving it).

However, within the lean4game framework, the formalization is necessarily provided as the `Statement`. The transfer happens at the conceptual level (reading the word problem, recognizing it as pigeonhole), which is valuable even if the Lean proof is mechanical. The extensive conclusion section with the paper-proof comparison does genuine transfer work.

**Where**: L09 -- no structural change needed, but the introduction could be more honest: "The Lean proof is the same as L08 -- the *mathematical* insight is recognizing that a room assignment is a function and applying pigeonhole."

**Effort**: Low (text edit).

**Recommend**: Consider.

---

### 9. The boss (L10) does not test proof-move V8 (witness extraction) or V9 (contradiction via cardinality), which are unique contributions of this world

**What**: The plan says W12's coverage includes V8 (choosing a witness from a nonempty finset, L04) and V9 (contradiction via cardinality, L05). The boss (L10) tests only cardinality computation (L01's `Fintype.card_sum`) combined with pigeonhole application (L08's collision form). V8 and V9 are never revisited after their introduction.

**Why**: L04 and L05 teach proof moves that the world promises to cover, but they are isolated: introduced once and never used again, not even in the boss. A boss that integrates all the world's lessons would be stronger. For example, a boss that requires the learner to (a) compute a cardinality, (b) apply pigeonhole to get a collision, and (c) use the collision to derive a further conclusion via witness extraction, would test L01-L05 and L06-L08 together. However, designing such a compound goal may be difficult within the lean4game framework.

**Where**: L10 -- consider whether the boss could incorporate a `obtain` step or a `Finset.card_eq_zero` step.

**Effort**: High (redesigning the boss).

**Recommend**: Consider. The current boss is a clean integration of counting + pigeonhole, which is the world's primary arc. V8 and V9 are supporting proof moves that will be used in later worlds (W12_ps). The boss does not need to test everything.

---

### 10. L04's `exact h` alternative is buried in the conclusion -- but it is the more elegant proof

**What**: L04's conclusion mentions that `exact h` works directly because `Finset.Nonempty s` is definitionally `exists x, x in s`. But the level teaches the `obtain` + `exact` two-step approach. The introduction explains this well ("the `obtain` version is more instructive because it mirrors the mathematical reasoning"). No change needed -- this is well-handled.

**Where**: N/A.

**Effort**: N/A.

**Recommend**: No action needed. Withdrawing this suggestion.

---

## R1 corrections (verified)

**R1-1 (L03 Option vs subtype)**: CONFIRMED. The plan specified L03 as "Cardinality of subtypes: Count elements of `{ x : Fin 5 // x.val % 2 = 0 }`". The world author used `Option` instead. The user's note explains this was due to subtype cardinality requiring `decide`/`native_decide` which are disabled. Given the disabled tactic constraints, `Option` is a reasonable alternative that still teaches compound-type cardinality (the `Fintype.card_option` lemma). The pedagogical value is preserved: learners see that `Option alpha` adds one element to `alpha`, which directly supports the pigeonhole setup (n+1 objects into n boxes). **No action needed.**

**R1-2 (L07 one-liner)**: CONFIRMED FALSE. L07's proof consists of 4 interactive steps: (1) `intro hinj`, (2) `have h := Fintype.card_le_of_injective f hinj`, (3) `rw [Fintype.card_fin, Fintype.card_fin] at h`, (4) `omega`. Each step has hints. The R1 reviewer was mistaken. **No action needed.**

---

## Overall impression

The world has a well-designed arc: three cardinality computation levels (L01-L03) build the counting toolkit, two proof-move levels (L04-L05) teach witness extraction and contradiction, and five pigeonhole levels (L06-L10) build from the specific case through the general theorem to applications and integration. The writing is clear, with good "plain language" summaries in conclusions and honest transfer moments. The L07 conclusion table comparing specific and general cases is a particularly nice pedagogical touch.

The single most important improvement is **adding `simp` to the `DisabledTactic` list on all levels** (suggestion 6). Without this, the cardinality levels (L01-L03) and possibly others can be bypassed by `simp`, undermining the named-lemma workflow. The second priority is **improving L08's introduction to explain the relationship between the two pigeonhole forms** (suggestion 4) -- the learner deserves to understand why their own `pigeonhole` theorem is being set aside in favor of a stronger mathlib lemma. Third is **verifying that `Fintype.card_fun` is a real mathlib name** (suggestion 1) -- a factual API error would be embarrassing.
