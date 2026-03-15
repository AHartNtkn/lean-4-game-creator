# Enrichment Review (Round 4): W3 ListBasics

This is a fourth-pass review following implementation of the three "Recommend: Yes" items from R3. The world now has 11 levels:

| # | File | Title |
|---|------|-------|
| 1 | L01_ListCons | The empty list and cons |
| 2 | L02_ListLength | Length of a cons |
| 3 | L03_ListMem | List membership |
| 4 | L04_MemAppend | Membership in an append |
| 5 | L05_ListMap | Map preserves membership |
| 6 | L06_ListFilter | Filtering a list |
| 7 | L07_AppendLength | Length of an append |
| 8 | L08_FinIndexing | Indexing with Fin |
| 9 | L09_Nodup | No duplicates |
| 10 | L10_Practice | Backward membership reasoning |
| 11 | L11_Boss | Boss: Map, filter, and membership |

## Assessment of R3 fixes

### R3 suggestion #1 (backward membership, L10): Well implemented

L10 now teaches `rw [...] at h` and `rcases h with h1 | h2` on the statement `a in l1 ++ l2 -> a in l2 ++ l1`. This exercises the backward direction of membership reasoning -- destructuring a hypothesis rather than building a goal. The proof has two clear steps: (1) unfold the hypothesis with `rw [List.mem_append] at h`, (2) case-split with `rcases`, then in each case unfold the goal and choose the opposite branch.

The introduction explains both new moves (`rw [...] at h` for hypothesis rewriting, `rcases h with h1 | h2` for case-splitting) before the learner needs them. The hints guide through each step. The conclusion names both skills explicitly and connects them to the forward direction already practiced. `rcases` gets a proper `TacticDoc` and is registered as a `NewTactic`.

This is the most important fix across all four rounds. The learner can now reason about membership in both directions, which is the dominant proof pattern in the downstream finset worlds (W6-W8). No further action needed.

### R3 suggestion #2 (Nodup failure case, L09): Well implemented

L09 now proves the conjunction `[1, 2, 3].Nodup /\ 1 in [2, 1]`. The first conjunct is the Nodup success case (unchanged from before); the second conjunct demonstrates the membership fact that blocks `[1, 2, 1].Nodup`. The conclusion connects the two: "you just proved `1 in [2, 1]`, which means `List.nodup_cons` applied to `1 :: [2, 1]` would require `1 not in [2, 1]` -- but you showed the opposite."

This satisfies the plan's requirement ("Prove a specific list has no duplicates, and show one that does") without adding a 12th level. The learner experiences both success and failure of the Nodup definition in a single level. No further action needed.

### R3 suggestion #3 (simp introduction, L09): Well implemented

L09's introduction now has a dedicated section titled "The `simp` tactic" that explains `simp` before the learner needs it. The text explains what `simp` does (applies a library of simplification lemmas), why it is appropriate here (concrete membership checks are mechanical), and where it will recur (later courses). This is better than introducing `simp` only in a mid-proof hint. No further action needed.

## Assessment of R3 "Consider" item (suggestion #4)

R3 suggestion #4 (Nodup conclusion citing the exact stuck goal state) was marked "Consider" and contingent on suggestion #2 not being adopted. Since suggestion #2 was adopted (the learner now proves `1 in [2, 1]` themselves), the conclusion no longer needs to show a hypothetical stuck state -- the learner has already done the work. The current conclusion correctly connects the two conjuncts. This item is resolved.

## New observations from R4 review

After reading all 11 levels in their current state, I have examined each of the enrichment lenses (mathematical depth, concrete examples, proof strategy enrichment, pedagogical opportunities, cross-world foreshadowing, Lean/tactic depth). Here are my findings.

### 1. L10's `rcases` documentation could mention the conjunction pattern

**What**: The `TacticDoc` for `rcases` says "More generally, `rcases` can destructure any inductive hypothesis. For conjunctions, use `<h1, h2>`; for disjunctions, use `h1 | h2`." But L10 only exercises the disjunction pattern. The conjunction pattern is used implicitly in L06 (where `constructor` builds a conjunction) but never destructured.

**Why**: In downstream worlds (W6-W8), the learner will regularly encounter hypotheses of the form `h : a in Finset.filter p s` which unfold to `a in s /\ p a`, requiring `rcases h with <hmem, hpred>`. The conjunction pattern for `rcases` is mentioned in the doc but never exercised. However, `constructor` (which is the dual of conjunction destructuring) has been used since L06, so the learner has some familiarity with conjunctions. And the doc does mention the pattern.

**Where**: L10 TacticDoc for `rcases`.

**Effort**: Low (already documented, no code change needed).

**Recommend**: No -- the doc already mentions it, and the downstream filter/membership levels will teach it in context. Forcing a conjunction destructuring into this level would muddy the clear focus on disjunction.

### 2. The world has no level that combines length and membership reasoning

**What**: L02 teaches `List.length_cons`, L07 teaches `List.length_append`, and L03-L06 teach membership reasoning. No level asks the learner to combine the two families of facts. The boss (L11) combines map, filter, and membership but does not involve length at all.

**Why**: Length and membership are the two main list properties this world covers, and a level combining them (e.g., "if `l` has length `n + 1`, then there exists some `a` and `l'` with `l = a :: l'`") would reinforce both. However, this kind of structural induction/decomposition is a step beyond what the world targets (the plan says "basic list operations"), and the boss already integrates 4 operations. Adding a length+membership combination would either require a 12th level or would displace existing content.

**Where**: Would be a new level, or a modification to L07.

**Effort**: Medium (new level or significant rework of L07).

**Recommend**: Consider. This is a genuine opportunity but not critical for the world's promise. The length lemmas are used in later worlds where the combination arises naturally.

### 3. The L11 boss does not exercise backward reasoning (L10's new skill)

**What**: L10 introduces backward membership reasoning (`rw [...] at h`, `rcases`), but L11 (the boss) uses only forward reasoning: rewrite the goal with `mem_filter`, split with `constructor`, rewrite with `mem_map`, provide a witness. The new skills from L10 are not tested in the boss.

**Why**: The boss should ideally integrate skills from across the world. L10's skills are the newest and most important addition (the dominant proof move for downstream worlds). If the boss does not exercise them, a learner who struggled on L10 has no reinforcement. However, the boss statement is well-crafted as a composition of map and filter membership, which is itself a meaningful integration. Forcing backward reasoning into the boss would require a different statement -- perhaps one where a hypothesis already contains `a in List.filter p l`, requiring destructuring.

**Where**: L11 (Boss).

**Effort**: Medium (redesigning the boss statement and proof).

**Recommend**: Consider. The current boss is a clean integration of L03-L06 skills. Adding L10's backward reasoning would make it more complete but also more complex. The downstream worlds (W4, W6-W8) will provide ample practice with backward reasoning, so the gap is not critical.

### 4. L08 (Fin indexing) is a one-tactic (`rfl`) level that could teach more about the Fin-List connection

**What**: L08 proves `[10, 20, 30].get <1, by norm_num> = 20` with `rfl`. The introduction and conclusion explain `List.get` and the connection to `Fin` from W1. But the proof itself involves no reasoning -- it is a definitional evaluation.

**Why**: This was noted in R2 (suggestion #8, "Consider") and R3 did not re-raise it. The level's pedagogical value comes from its exposition (what `List.get` is, how `Fin` enforces bounds), not from its proof. A level that required actual reasoning about `List.get` would need lemmas like `List.get_cons_succ` or `List.get_map`, which are deeper than the world targets. The level works well as a "connection moment" that ties back to W1 without overloading the learner.

**Where**: L08.

**Effort**: Medium (would need a lemma-based proof rather than `rfl`).

**Recommend**: No. The level serves its connection purpose. Deeper `List.get` reasoning belongs in a later world if needed.

### 5. L04 teaches the forward direction of `mem_append` but L10 now teaches the backward direction -- the symmetry could be called out

**What**: L04 proves `a in l1 -> a in l1 ++ l2` (forward direction of `mem_append`). L10 proves `a in l1 ++ l2 -> a in l2 ++ l1` (which requires the backward direction). The connection between these two levels is not explicitly mentioned.

**Why**: The conclusion of L10 refers back to "every level so far" having been forward reasoning, but does not specifically call out L04 as the forward counterpart. A sentence like "In Level 4, you used `mem_append` to prove membership in a concatenation. Here, you used it in the opposite direction -- to decompose a concatenation membership into cases." would make the symmetry explicit.

**Where**: L10 conclusion.

**Effort**: Low (one sentence in the conclusion).

**Recommend**: Consider. The current conclusion is already well-written and explains the forward/backward distinction clearly. The specific callback to L04 would add a nice thread but is not essential.

## Overall impression

The world is now in excellent shape. All three R3 "Recommend: Yes" items have been implemented well:

- L09 has a proper `simp` introduction section, the Nodup success case, and the Nodup failure demonstration (`1 in [2, 1]`), satisfying the plan's requirement.
- L10 teaches backward membership reasoning with `rw [...] at h` and `rcases`, the most important proof move for downstream worlds.
- `rcases` is properly documented with a `TacticDoc`.

The level ladder has a clean arc:
1. Construction (L01: cons and list literals)
2. Symbolic reasoning (L02: `length_cons`, L03: `mem_cons`)
3. Composition (L04: `mem_append`, L05: `mem_map`, L06: `mem_filter`)
4. Structural properties (L07: `length_append`, L08: `List.get` connecting to Fin)
5. Refinement (L09: `Nodup` with success and failure cases, introducing `simp`)
6. Proof direction (L10: backward reasoning with `rw at` and `rcases`)
7. Integration (L11: boss combining map, filter, and membership)

Every level teaches a genuine proof move (no `decide`/`simp`-only proofs except where deliberately introduced). `simp` is introduced with proper exposition. `aesop` and `decide` are disabled throughout. The writing is clear, with consistent "in plain language" summaries, accurate foreshadowing to downstream worlds, and honest transfer moments.

The suggestions marked "Consider" above (length+membership combination, boss exercising backward reasoning, L04-L10 callback) are genuine opportunities but none is critical. The world delivers on its promise: "The learner can construct lists, reason about membership, and use basic list operations."

**Verdict: The world is clean. No "Recommend: Yes" items remain.**
