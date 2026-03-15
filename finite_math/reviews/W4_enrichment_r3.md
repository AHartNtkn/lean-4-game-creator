# W4 MultisetHierarchy -- Enrichment Review (Round 3)

## R1/R2 suggestions: status check

The world has been substantially rebuilt since R1. What was a 9-level definition tour is now a 14-level world with genuine proof-move teaching. Here is the status of each R1 suggestion:

| R1 # | Suggestion | Status | Notes |
|-------|-----------|--------|-------|
| 1 | Add symbolic `count` level (`count_cons_self`/`count_cons_of_ne`) | **Done** | L07 (CountSymbolic) teaches both lemmas with `norm_num` disabled |
| 2 | Prove `[1,2,3] ≠ [3,1,2]` alongside multiset equality | **Done** | L04 (InformationLossLists) proves the conjunction |
| 3 | Add cardinality inequality (`toFinset_card_le`) | **Done** | L11 (CardinalityInequality) teaches derive-then-instantiate with `omega` disabled |
| 4 | Connect `Multiset.Nodup` back to `List.Nodup` | **Done** | L12 (NodupConnection) proves both directions + `toFinset_val` |
| 5 | Name the "reduce-then-compute" proof strategy | **Done** | L13 (ReduceThenCompute) formally names it with examples from all prior levels |
| 6 | Add `Multiset.mem` / `mem_coe` level | **Done** | L02 (MultisetMem) teaches `mem_coe` with reduce-then-compute |
| 7 | Boss requires non-`decide` steps | **Done** | L14 boss requires `card_map`, `map_coe`, `coe_eq_coe`, and `toFinset_card_le` |
| 8 | Foreshadow `Finset.image` in L03 conclusion | **Done** | L05 conclusion mentions `Multiset.filter` and foreshadows cardinality behavior |
| 9 | "What if" level: toFinset on Nodup multiset | **Not done** | Was "Consider" -- reasonable to skip |
| 10 | Vocabulary seed `Multiset.filter` | **Done** | L05 conclusion mentions it |
| 11 | Definitional equality explanation in L01 | **Done** | L01 conclusion explains definitional vs propositional equality |

R2 changes (per user context):
- L07: `norm_num` added to DisabledTactic -- **Confirmed** (line 108)
- L07: Paragraph explaining why `rfl`/`decide` works after symbolic rewrites -- **Confirmed** (conclusion lines 82-86)
- L11: `omega` added to DisabledTactic -- **Confirmed** (line 83)
- L14 boss has comprehensive skills table -- **Confirmed** (lines 91-106)

**Summary**: All "Yes" suggestions from R1 have been implemented. All R2 changes are in place. The world has been transformed from a definition tour into a genuine lecture world with proof-move teaching, scaffold fade, and a well-designed boss.

---

## New suggestions for R3

### 1. L05 disables `decide` -- but the intended second step is `rfl`, not a symbolic move; consider adding a note about why `decide` is off

**What**: L05 (MultisetOperations) disables `decide` in its `DisabledTactic` line, which is correct to prevent one-shot bypass. But the introduction and hints never explain why `decide` is disabled here when it was used freely in L02-L04. A learner who has been using `decide` as their go-to closer will be confused when it suddenly does not work.

**Why**: The learner's mental model at this point is "concrete propositions can always be closed with `decide`." L05 is the first level where `decide` is withheld, and the shift from `decide` to `rfl` as the closing move is pedagogically significant: it teaches that some equalities are *definitional* (closed by `rfl`) while others are only *decidable* (closed by `decide`). But this distinction is never articulated at the point where the learner first encounters it. L01 discusses definitional equality, but L05 does not remind the learner why `rfl` is preferred here.

**Where**: Add 1-2 sentences to L05's first `Hint` or introduction, e.g.: "After `rw [Multiset.card_map]`, the goal becomes a definitional equality. Use `rfl` (not `decide`) to close it -- this reinforces that `Multiset.card` on a coerced list equals the list's length by definition."

**Effort**: Low (a sentence in a hint)

**Recommend**: Consider

---

### 2. L02 enables `decide` but L05 disables it -- the inventory change is invisible to the learner

**What**: The `DisabledTactic` line varies across levels: L01 disables `decide`, L02-L04 allow it, L05 disables it again, L06 allows it, L07 disables it, etc. This on-off pattern is never explained. A learner may try `decide` in L05, get an error, and not understand why it worked in L04 but not L05.

**Why**: The on-off `decide` pattern is pedagogically motivated (disable it when it would bypass the lesson), but the learner has no way to know this. In the game interface, disabled tactics produce error messages, but the error does not say "this tactic is disabled for pedagogical reasons." A single sentence in the introduction of L05 or L07 acknowledging the restriction would prevent confusion.

**Where**: Add a note to the first level where `decide` is disabled after having been available (L05), e.g.: "In this level, `decide` is disabled so that you practice the structural rewrite. You will use `decide` again in later levels."

**Effort**: Low (a sentence)

**Recommend**: Consider

---

### 3. L04 could benefit from a concluding remark connecting to the mathematical concept of quotient maps

**What**: L04 proves that different lists map to the same multiset (many-to-one). The conclusion says "it is a many-to-one function" but does not use the word "quotient" in this context, even though L01 introduced `Multiset α := Quot (List.Perm)`.

**Why**: The word "quotient" was introduced in L01 as a definition, but L04 is where the learner first *experiences* what quotient means operationally (distinct representatives mapping to the same equivalence class). Connecting L04's concrete experience back to L01's abstract definition ("This is what it means for `Multiset` to be a quotient: different lists are identified when they are permutations") would close the conceptual loop. This is a transfer opportunity: in mathematics, quotient constructions appear everywhere (cosets, equivalence relations, modular arithmetic), and naming the pattern here prepares the learner.

**Where**: Add 1-2 sentences to L04's conclusion.

**Effort**: Low (a sentence in conclusion)

**Recommend**: Consider

---

### 4. L09 conclusion could note that `List.toFinset` composes both steps, connecting to the explicit two-step path

**What**: L09 introduces `List.toFinset` as a "shortcut" that goes directly from list to finset. The `DefinitionDoc` mentions it is "equivalent to `Multiset.toFinset (↑l)`", which is good. But the conclusion does not make the learner prove or even state this equivalence. A concluding remark like "You could also have written `Multiset.toFinset (↑[1, 2, 3]) = Multiset.toFinset (↑[3, 2, 1, 2])` and arrived at the same result -- `List.toFinset` is simply the composition of `↑` and `Multiset.toFinset`" would reinforce the hierarchy.

**Why**: The hierarchy is the world's central narrative, and L09 is the last pure "information loss" level before L10 compares all three layers. Making the two-step decomposition explicit here, right before L10 puts everything together, would strengthen the narrative arc.

**Where**: Add 1-2 sentences to L09's conclusion.

**Effort**: Low (a sentence)

**Recommend**: Consider

---

### 5. L13 (ReduceThenCompute) uses `Multiset.map_coe` without prior introduction

**What**: L13 introduces `Multiset.map_coe` as a new theorem (via `NewTheorem Multiset.map_coe`) and uses it as the first rewrite step. But this is the first time the learner encounters `map_coe`. The level's pedagogical goal is to *practice the named pattern*, not to learn a new bridge lemma. Introducing a new lemma in a practice/consolidation level dilutes the lesson.

**Why**: L13 is supposed to be the "naming" level for the reduce-then-compute pattern. It should ideally use only tools the learner already has, applying them in a slightly new configuration that exercises the named strategy. Introducing `map_coe` here means the level is doing double duty: teaching a new lemma AND naming a strategy. The level would be cleaner if `map_coe` had been introduced earlier (e.g., in L05 alongside `card_map`, since both are about `Multiset.map` on coerced lists) and L13 simply recalled it.

**Where**: Consider moving the `NewTheorem Multiset.map_coe` introduction and its `TheoremDoc` to L05 (where `Multiset.map` and `card_map` are taught), and have L13 simply use it as a known tool. Alternatively, split L13 into two parts: first introduce `map_coe`, then use it in the pattern exercise. If neither change is worth the effort, at minimum add a `TheoremDoc` note in L05 foreshadowing that `map_coe` exists.

**Effort**: Medium (move theorem declaration between levels)

**Recommend**: Yes

---

### 6. L11 uses `exact` with a general theorem but does not contrast with `apply`

**What**: L11 teaches the "derive-then-instantiate" pattern using `exact Multiset.toFinset_card_le _`. But the level does not mention that `apply Multiset.toFinset_card_le` would also work (and would let Lean infer the argument entirely). The distinction between `exact` (provide the full term) and `apply` (provide the head and let Lean fill in arguments) is a useful Lean skill.

**Why**: This is a minor point. The learner already knows `exact` and `apply` from prerequisites. But L11 is a natural place to remind them that `apply` is often more convenient when a lemma's argument can be inferred. A hint variant or conclusion note saying "You could also have written `apply Multiset.toFinset_card_le` without the underscore" would reinforce tactic fluency.

**Where**: L11 conclusion, one sentence.

**Effort**: Low (one sentence)

**Recommend**: Consider

---

### 7. The boss (L14) does not test `mem_coe` (L02) or `coe_nodup` (L12)

**What**: The boss tests `card_map` (L05), `map_coe` + `coe_eq_coe` (L03, L13), and `toFinset_card_le` (L11). It does not test `mem_coe` (L02), `count_cons_self` (L07), or `coe_nodup` (L12). Three of the world's 13 pre-boss levels contribute no skill to the boss.

**Why**: The boss already has three conjuncts and requires four distinct proof moves, which is a reasonable integration demand for a 14-level world. Adding more conjuncts would risk making the boss feel like a laundry list. However, the absence of any `mem_coe` or counting skill in the boss means those skills are not tested under integration pressure. This is a minor gap -- the skills are tested in isolation in their respective levels -- but it is worth noting.

**Where**: If the boss were to be expanded, a fourth conjunct testing `mem_coe` (e.g., `1 ∈ m₂`) would be natural and short. But this is not strongly recommended given the boss is already well-designed.

**Effort**: Medium (add a conjunct to the boss)

**Recommend**: Consider

---

### 8. No level exercises `count_cons_of_ne` -- only `count_cons_self` is practiced

**What**: L07 introduces both `Multiset.count_cons_self` and `Multiset.count_cons_of_ne` (both in the `NewTheorem` line and documented). But the proof only uses `count_cons_self`. The learner sees `count_cons_of_ne` in the documentation but never uses it.

**Why**: `count_cons_of_ne` is the more interesting of the two lemmas because it requires a hypothesis `h : a ≠ b`. Using it in a proof would teach the learner to provide a proof of inequality as an argument to a rewrite, which is a genuinely new proof move (providing a hypothesis argument to a rewrite lemma). `count_cons_self` has no hypothesis -- it is simpler. The world would be stronger if L07 had a second part (or a follow-up exercise) requiring `count_cons_of_ne`.

**Where**: Extend L07 to a two-part proof, or add a follow-up level. For example: "Prove `Multiset.count 2 (1 ::ₘ ↑[2, 3]) = 1`" which requires `rw [Multiset.count_cons_of_ne (by decide : (2 : Nat) ≠ 1)]` then `decide`. This would teach the learner to provide the `h : a ≠ b` proof.

**Effort**: High (new level or significant level extension)

**Recommend**: Yes

---

## Overall impression

The world has improved dramatically since R1. What was a 9-level definition tour with zero proof-move teaching is now a 14-level lecture world with a clear scaffold fade (computational levels L01-L06, symbolic reasoning L07-L12, pattern consolidation L13, integration boss L14), explicit strategy naming (L13's reduce-then-compute), and a boss that genuinely integrates skills from earlier levels. The R1 and R2 suggestions have been implemented thoroughly.

The two "Yes" suggestions remaining are:

1. **Move `map_coe` introduction from L13 to L05** -- L13 should be a consolidation level, not a new-lemma-introduction level. This is a relatively small structural change.

2. **Add a `count_cons_of_ne` exercise** -- the world introduces the lemma but never practices it. The `of_ne` variant is more interesting than `cons_self` because it requires a hypothesis argument, and the world currently has a gap where this proof shape is taught in documentation but never exercised.

The "Consider" items are all minor text additions (1-2 sentences each) that would improve cohesion and learner experience but are not essential. None represent structural gaps.

**The single most important improvement** is suggestion #8 (exercising `count_cons_of_ne`). The world currently documents a lemma that requires a hypothesis argument but never makes the learner use it. This is a genuine proof-move gap: providing `(h : a ≠ b)` as an argument to a rewrite lemma is a new skill that the learner will need in later worlds (e.g., `Finset.mem_insert_of_ne`, `Finset.card_insert_of_not_mem`). Teaching it here, in a simple concrete setting, would prepare the learner for these more complex applications.
