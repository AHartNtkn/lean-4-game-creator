# W4 MultisetHierarchy -- Enrichment Review (Round 2)

## R1 implementation status

All R1 "Yes" suggestions were implemented. Summary:

| R1# | Suggestion | Status | Implementation |
|-----|-----------|--------|---------------|
| 1 | Count symbolic level | **Done** | L07 (CountSymbolic) -- `count_cons_self` + `decide` |
| 2 | List inequality level | **Done** | L04 (InformationLossLists) -- conjunction `≠ ∧ =` |
| 3 | Card toFinset inequality | **Done** | L11 (CardinalityInequality) -- `exact toFinset_card_le _` |
| 4 | Nodup connection | **Done** | L12 (NodupConnection) -- `coe_nodup` + `toFinset_val` |
| 5 | Reduce-then-compute naming | **Done** | L13 (ReduceThenCompute) -- dedicated level naming the pattern |
| 6 | Multiset.mem | **Done** | L02 (MultisetMem) -- `rw [mem_coe]; decide` |
| 7 | Boss redesign | **Done** | L14 (Boss) -- three-part conjunction requiring `card_map`, `map_coe` + `coe_eq_coe`, `toFinset_card_le` |

R1 "Consider" suggestions:

| R1# | Suggestion | Status | Notes |
|-----|-----------|--------|-------|
| 8 | Foreshadowing `Finset.image` in L03 | **Done** | L05 conclusion mentions `Multiset.filter` and foreshadows W8 |
| 9 | "What if" level: toFinset on Nodup multiset | **Partially** | L11 conclusion mentions equality holds when `Nodup`, but no dedicated level |
| 10 | Vocabulary seeding for `Multiset.filter` | **Done** | L05 conclusion seeds `Multiset.filter` |
| 11 | Definitional equality note in L01 | **Done** | L01 intro and conclusion both explain why `rfl` works |

The world has been substantially improved. It grew from 9 to 14 levels, with meaningful proof-move content added throughout.

---

## Ranked suggestions

### 1. No `Branch` hints anywhere in the world

**What**: None of the 14 levels have `Branch` hints catching common wrong moves. Multiple levels have natural wrong-move scenarios that should have rescue paths.

**Why**: The R1 playtest audit (P2-4) flagged this. The rewrite addressed strategy-level hints (good), but `Branch` hints are still absent. In levels with multi-step proofs, a learner who tries the wrong first step gets no feedback -- only a stuck state. Specific scenarios:

- L02: Learner tries `decide` instead of `rw [Multiset.mem_coe]` first. `decide` is available here (not disabled). If the learner uses `decide` directly, they bypass `mem_coe` entirely. A `Branch` after `decide` saying "That works for concrete examples, but the technique in this level -- using `rw [Multiset.mem_coe]` to reduce to list membership -- is what you need for non-concrete multisets" would preserve the lesson.
- L04: Learner tries `decide` on the full conjunction (which works, since `decide` is not disabled). Same issue.
- L07: Learner tries `decide` on the whole goal (disabled, so they get stuck). A `Branch` catching the `decide` attempt with "This level has `decide` disabled to encourage symbolic reasoning. Use `rw [Multiset.count_cons_self]` to peel off the matching element first" would help.
- L12: Learner tries `decide` on the Nodup goal directly instead of `rw [Multiset.coe_nodup]` first.
- L13: Learner tries `rw [Multiset.coe_eq_coe]` before `rw [Multiset.map_coe]` -- gets stuck because the left side still has `Multiset.map`.

**Where**: L02, L04, L07, L12, L13 at minimum.

**Effort**: Medium (multiple levels need `Branch` blocks added)

**Recommend**: Yes

---

### 2. L02, L04, L06, L08, L09, L12 do not disable `decide`, allowing one-shot bypass of intended proof

**What**: Six levels have `DisabledTactic` lines that do NOT include `decide`. In each of these levels, `decide` can one-shot the goal, bypassing the intended proof path that teaches a specific bridge lemma or proof structure.

**Why**: The R1 playtest audit (P0-2) flagged `decide` exploitability across levels where it was not intended. The rewrite correctly disabled `decide` on L01, L05, L07, L10, L11, L13, L14 -- but left it available on L02, L03, L04, L06, L08, L09, L12. In these levels:

| Level | Intended proof | `decide` bypass |
|-------|---------------|----------------|
| L02 | `rw [Multiset.mem_coe]; decide` | `decide` alone closes it, bypassing `mem_coe` |
| L04 | `constructor` + `decide` + `rw [coe_eq_coe]; decide` | `decide` alone closes the whole conjunction |
| L06 | `decide` | `decide` **is** the intended tactic here -- no issue |
| L08 | `decide` | `decide` **is** the intended tactic here -- no issue |
| L09 | `decide` | `decide` **is** the intended tactic here -- no issue |
| L12 | `constructor` + `rw [coe_nodup]; decide` + `exact toFinset_val _` | `decide` alone closes the whole conjunction |

L06, L08, L09 use `decide` as the intended proof, so they are fine. But L02, L04, and L12 have `decide` as a one-shot bypass of their pedagogical content.

- L02: The whole point is to learn `rw [Multiset.mem_coe]`. If `decide` closes it in one shot, the learner never sees the bridge lemma.
- L04: The intended proof requires `constructor` + `rw [Multiset.coe_eq_coe]`. `decide` bypasses both.
- L12: The intended proof uses `rw [Multiset.coe_nodup]` and `exact Multiset.toFinset_val _`. `decide` bypasses both.

**Where**: L02, L04, L12. Add `decide` to their `DisabledTactic` lines.

**Effort**: Low (one-line change per file)

**Recommend**: Yes

---

### 3. L03 does not disable `decide`, allowing bypass of `coe_eq_coe`

**What**: L03 (PermAndEquality) teaches `rw [Multiset.coe_eq_coe]` as the bridge from multiset equality to list permutation, but `decide` is not disabled and closes the goal in one shot.

**Why**: This is the same issue as #2 but deserves separate mention because L03 is the first level that introduces `Multiset.coe_eq_coe` -- one of the most important bridge lemmas in the world. If the learner skips it by typing `decide`, the entire "permutation bridge" lesson is lost. The intended proof is `rw [Multiset.coe_eq_coe]; decide`, but `decide` alone suffices.

**Where**: L03. Add `decide` to the `DisabledTactic` line.

**Effort**: Low (one-line change)

**Recommend**: Yes

---

### 4. The `count_cons_of_ne` lemma is introduced but never exercised

**What**: L07 introduces both `Multiset.count_cons_self` and `Multiset.count_cons_of_ne` (via `NewTheorem`), but the level only exercises `count_cons_self`. The learner never uses `count_cons_of_ne` in any level.

**Why**: Introducing a theorem in the inventory but never requiring the learner to use it is a pedagogical gap. The pair `count_cons_self` / `count_cons_of_ne` are described as the "recursive recipe" for counting (L07 conclusion), but only half the recipe is ever practiced. A level or a conjunct in the boss that requires `rw [Multiset.count_cons_of_ne (by decide : (2 : Nat) ≠ 1)]` would complete the pair and give the learner experience providing a proof of the inequality hypothesis.

This is also a missed opportunity to teach an important Lean skill: providing a proof argument to a rewrite lemma (`rw [lemma_name proof_arg]`). The `count_cons_of_ne` lemma requires a proof `h : a ≠ b`, which means the learner must write something like `rw [Multiset.count_cons_of_ne (by decide)]`. This is a new proof move -- it combines `rw` with a side goal -- and would be more instructive than any level currently in the world.

**Where**: New level after L07, or add a conjunct to the boss. A natural exercise: prove `Multiset.count 1 (2 ::ₘ 1 ::ₘ ↑[3] : Multiset Nat) = 1`, requiring `rw [Multiset.count_cons_of_ne ...]` then `rw [Multiset.count_cons_self]` then `decide`.

**Effort**: High (new level) or Medium (add boss conjunct)

**Recommend**: Yes

---

### 5. L05 (MultisetOperations) conclusion foreshadows `Multiset.filter` but mentions "W8" -- the foreshadowing should name the destination world, not a number

**What**: L05's conclusion says "You will encounter it in a later world" for `Multiset.filter`, which is good. But the learner has no way to know what "a later world" means. The foreshadowing should name the destination concept or world title, not a number.

**Why**: Foreshadowing is only effective when it gives the learner a hook to recognize the callback. "You will encounter `Multiset.filter` when working with finset operations" is actionable; "in a later world" is vague. The learner will have forgotten this foreshadowing by the time they reach the relevant world unless the future context is named.

**Where**: L05 conclusion, modify the foreshadowing sentence.

**Effort**: Low (one sentence)

**Recommend**: Consider

---

### 6. The world introduces `Multiset.map_coe` only in L13 -- late for a bridging lemma used in the boss

**What**: `Multiset.map_coe` is first used in L13 (ReduceThenCompute) and then again in L14 (Boss). It appears in the `NewTheorem` declaration of L13, meaning the learner first sees it only two levels before the end. The boss immediately requires it.

**Why**: The boss tests integration of skills from earlier levels. If `map_coe` is introduced in L13 and tested in L14, there is no practice gap -- the learner uses it once and immediately has to recall it in a multi-step proof. Compare with `coe_eq_coe` (introduced L03, used repeatedly through L04, L13, L14) or `card_map` (introduced L05, tested L14). Those have multiple practice opportunities between introduction and boss. `map_coe` has zero practice opportunities. Consider moving it earlier (e.g., to L05, since L05 already covers `Multiset.map` and `card_map`) or adding a practice exercise between L13 and L14.

**Where**: Either move `map_coe` to L05 or add a brief exercise in L13 that uses both `map_coe` and `coe_eq_coe` in a simpler context before the boss demands it.

**Effort**: Medium (restructure L05 or L13)

**Recommend**: Consider

---

### 7. No `NewTactic` declarations anywhere in the world

**What**: The world uses `rfl`, `decide`, `rw`, `constructor`, and `exact` but never declares any of them via `NewTactic`. While these were presumably introduced in earlier worlds, the game framework expects tactics used in hints to have been declared somewhere in the prerequisite chain.

**Why**: The lesson learned from W3 (documented in memory) is: "Always add `NewTactic` for tactics used in hints." If any of these tactics were not declared in W1/W2/W3, the build may warn about missing tactic documentation. Even if they were declared earlier, it is worth verifying that the prerequisite chain covers all of them. This is a maintenance concern, not a pedagogical one, but it affects build cleanliness.

**Where**: Verify that `rfl`, `decide`, `rw`, `constructor`, `exact` all have `TacticDoc` and `NewTactic` declarations in earlier worlds. If any are missing, add them to L01 of this world.

**Effort**: Low (verification + possible one-line additions)

**Recommend**: Consider

---

### 8. L09 (InformationLossFinset) is purely computational -- no proof move distinct from L06

**What**: L09 proves `([1, 2, 3] : List Nat).toFinset = ([3, 2, 1, 2] : List Nat).toFinset` using just `decide`. L06 (CountCompute) also uses just `decide`. These two levels teach different *concepts* (counting vs information loss) but use identical *proof moves*.

**Why**: The world now has a good gradient from computational to symbolic levels, but L09 sits between the conceptually rich L08 (toFinset) and L10 (ThreeLayers), contributing a computation exercise that is indistinguishable in proof technique from L06. The *concept* is important (different lists giving the same finset), but could it be taught with a richer proof? For instance: prove the conjunction `([1, 2, 3] : List Nat).toFinset = ([3, 2, 1, 2] : List Nat).toFinset ∧ [1, 2, 3] ≠ ([3, 2, 1, 2] : List Nat)`, paralleling L04's structure. This would reinforce the information-loss conjunction pattern from L04 and create a deliberate echo between L04 (List→Multiset information loss) and L09 (List→Finset information loss).

**Where**: Modify L09 statement to a conjunction.

**Effort**: Medium (modify statement and proof)

**Recommend**: Consider

---

### 9. The world's transfer moment is only in the boss conclusion -- consider making it more prominent

**What**: The plan specifies a transfer moment: "In ordinary math, we often say 'the set of elements in the list.' In Lean, that's `toFinset`, and it drops duplicates and forgets order." This appears in the L14 conclusion under "Transfer to paper proofs," but nowhere else in the world.

**Why**: Transfer is one of the five layers the course must cover. Having a single transfer paragraph in the boss conclusion is adequate but not ideal. The most natural transfer moment is L08 or L09, where `toFinset` first appears and the learner can be explicitly told: "When you write '{1, 2, 3}' in a paper proof to describe the distinct elements of some sequence, you are implicitly performing this `toFinset` operation." Placing the transfer closer to the concept's introduction (rather than only in the boss recap) helps the learner make the connection while the concept is fresh.

**Where**: Add 1-2 transfer sentences to L08 or L09 conclusion.

**Effort**: Low (conclusion text)

**Recommend**: Consider

---

## Overall impression

The R1 rewrite substantially improved this world. It went from a 9-level "definition tour" where every level was closed by `rfl` or `decide` to a 14-level world with genuine proof-move teaching: symbolic counting (L07), bridge-lemma rewriting (L02, L03, L05, L12, L13), theorem application (L11), and a multi-technique boss (L14). The level naming is clean and descriptive. The prose is consistently high quality -- introductions set up the concept, conclusions recap the proof move, and foreshadowing connects to later worlds. The "reduce-then-compute" naming in L13 is excellent pedagogy: it gives the learner a reusable handle for a proof pattern that recurs throughout the course.

The single most important improvement remaining is **closing the `decide` exploit on L02, L03, L04, and L12** (suggestions #2 and #3). These four levels have `decide` available and closable in one shot, which means the learner can bypass the bridge lemmas (`mem_coe`, `coe_eq_coe`, `coe_nodup`) that are the world's primary pedagogical content. Without disabling `decide` on these levels, the world's proof-move layer remains optional for a learner who discovers `decide` works. This is a carry-over from R1 (P0-2) that was partially but not fully addressed.

The secondary priority is **adding `Branch` hints** (#1) and **exercising `count_cons_of_ne`** (#4). The first improves recoverability for stuck learners; the second completes the "recursive recipe" for counting that L07 promises but only half-delivers.
