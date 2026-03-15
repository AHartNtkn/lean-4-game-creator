# W10_ps FinsetPset — Enrichment Review (Round 1)

## Ranked suggestions

### 1. L05 proves a trivially true arithmetic identity — the induction adds nothing

**What**: Replace the L05 target `s.card <= s.card + s.card` with a statement where induction is actually necessary (e.g., a property that requires reasoning about `a \notin s'` in the inductive step).

**Why**: The current target is provable by `omega` alone — the finset induction is entirely unnecessary because the conclusion is a pure `Nat` inequality independent of finset structure. A pset level should force genuine retrieval of finset induction, not let the learner route around it. The plan says this level should be "retrieval of V4" (finset induction on a fresh target), but a target that `omega` closes without induction does not test that retrieval. A better target would involve finset-specific reasoning in the inductive step, such as: for all finsets `s` of natural numbers, `s.filter (fun x => x > 0)` is a subset of `s`, proved by induction; or every finset satisfies `(s.image id).card <= s.card`; or some property where the `a \notin s'` hypothesis must actually be used (e.g., relating `(insert a s').card` to `s'.card`).

**Where**: L05

**Effort**: Medium (new statement and proof, same level structure)

**Recommend**: Yes

---

### 2. The boss (L08) mixes concrete and abstract parts in a way that dilutes the integration test

**What**: Make all three parts of the boss require multi-step reasoning rather than one-lemma closures. Part 2 (`s \cap t \subseteq s`) is a two-line proof; Part 3 is `have h := ...; omega`. Neither tests integration under pressure.

**Why**: The plan says the boss should be "a proof combining 4+ moves from Modules B--C." The current boss technically touches 4+ moves, but two of the three parts are trivial applications of single lemmas. A true pset boss should require the learner to chain moves without the level itself decomposing the problem into independent subparts. Consider replacing the three-part conjunction with a single multi-step goal that requires the learner to decide when to use membership rewriting, subset reasoning, cardinality monotonicity, and set operations — all within one proof, where the `refine` split is part of the challenge, not given by the statement structure.

**Where**: L08

**Effort**: High (redesign the boss statement)

**Recommend**: Yes

---

### 3. L06 is a one-line `exact` — too little retrieval for a pset

**What**: Require the learner to do more work than `exact Finset.card_union_add_card_inter _ _`. For example, ask them to first compute the union and intersection concretely (using `ext` + membership), then apply inclusion-exclusion, then verify the numerical identity.

**Why**: This is a pset world — reduced scaffolding, genuine retrieval. But L06's proof is literally `exact Finset.card_union_add_card_inter _ _`. The transfer content in the conclusion is excellent, but the level itself tests only "do you remember the lemma name?" A pset level should require reassembling the proof move, not just recalling a lemma. Even a two-step version — first compute `({7,8,9} \cup {9,10,11}).card` by determining the union explicitly, then verify the equation — would make the retrieval more meaningful.

**Where**: L06

**Effort**: Medium (rework the statement so the learner must do concrete computation before or after applying the lemma)

**Recommend**: Yes

---

### 4. L07 gives the subset hypothesis for free — the learner should prove it

**What**: Remove `h` from the hypotheses and require the learner to prove both `{100, 200} \subseteq {100, 200, 300, 400}` and the cardinality inequality.

**Why**: The plan says this level retrieves V14 (subset proof) and T3 (transfer). But the subset `h` is given as a hypothesis, so V14 is never actually retrieved — the learner just applies `Finset.card_le_card h`. In a pset, the learner should construct the subset proof themselves, then apply the cardinality lemma. This would genuinely test both V14 and V15 retrieval.

**Where**: L07

**Effort**: Low-medium (change the statement to not include `h`, adjust the proof to first prove the subset)

**Recommend**: Yes

---

### 5. L01 and L02 are essentially the same proof shape as the lecture levels — the "fresh surface form" is just different numbers

**What**: For at least one of L01/L02, use a fresh *proof context* rather than just fresh numbers. For example, L01 could require proving membership in a finset that was constructed via `insert` or `filter` rather than a literal, or L02 could prove a subset where the smaller set is obtained by filtering the larger set.

**Why**: The plan says pset levels should have "fresh surface forms." Currently, L01 changes `{1,2,3}` to `{10,20,30,40}` and L02 changes `{1,2,3}` to `{5,10,15,20}`. These are different numbers but identical proof shapes. Genuine surface-form variation means changing the *form of the goal* — e.g., the finset is built by `Finset.cons` instead of literal notation, or the membership target is a variable rather than a literal. The learner who can only handle `{a, b, c}` literals has not truly retrieved the membership proof move.

**Where**: L01 and/or L02

**Effort**: Medium (new statement with a different construction path)

**Recommend**: Consider

---

### 6. Missing: a level that combines set operations with cardinality in a non-trivial way

**What**: Add a level (or rework L04) where the learner must combine a set operation (e.g., union or intersection) with a cardinality computation, requiring both `ext`/membership reasoning and `card` reasoning in the same proof.

**Why**: The plan's coverage map shows V5, V6, V7, V14, M8, M9 all at Transfer stage in this world. But none of the current levels require the learner to combine set-operation reasoning with cardinality in a single proof (L04 is filter+card, which is close but uses `ext` only to identify the filter result, not to reason about set operations). A level like "Prove that `({1,2,3} \cup {3,4,5}).card = 5`" — where the learner must first determine the union, then compute its cardinality — would integrate V6 with M9 in a way no current level does.

**Where**: New level (between L03 and L04, or replacing L04)

**Effort**: Medium (new level)

**Recommend**: Consider

---

### 7. L03 (absorption law) is a good level but the conclusion could name the strategy pattern

**What**: In L03's conclusion, name the proof strategy: "element-chasing via `ext`" or "extensionality proof." Articulate that the pattern — `ext`, split the iff, prove each direction by membership rewriting — is a strategy that applies to *any* finset equality.

**Why**: The conclusion says "the same `ext` + membership-rewriting technique you learned in W7" but does not name the pattern. The skill instructions note that unnamed strategies are an enrichment opportunity. This is a pset world, so the conclusion should reinforce the strategy name for transfer to later worlds. The same pattern will reappear in Module D (when proving fintype-related equalities) and Module E (when working with `Finset.sum`).

**Where**: L03 conclusion

**Effort**: Low (add 1-2 sentences to the conclusion)

**Recommend**: Yes

---

### 8. L04 uses `omega` for the filter identification — the learner should be nudged toward `simp` + `Finset.mem_filter`

**What**: Adjust the hint and model solution so the learner practices the explicit `Finset.mem_filter` rewriting rather than hiding everything inside `omega`. The pset should retrieve the filter membership lemma explicitly.

**Why**: The model solution uses `ext x; simp only [Finset.mem_filter, ...]; omega`. The `omega` here is doing the numeric comparison work, which is fine, but the hidden hint says "use `have` to show the filter equals the expected finset, then `rw` and compute." This does not tell the learner to use `Finset.mem_filter`. Since this is a retrieval level for M8 (filter), the hint should explicitly guide toward the `mem_filter` rewriting step. The current approach hides the very thing being retrieved.

**Where**: L04 hint

**Effort**: Low (reword the hint)

**Recommend**: Yes

---

### 9. The boss conclusion's retrieval table references wrong worlds

**What**: The boss conclusion (L08) says "L01: Membership rewriting (V5) — From world W6" and "L02: Subset proofs (V14) — From world W7". But within this course, membership is taught in W6 and subset in W7 — these are correct. However, L05 says "Finset induction (V4) — W10" and L07 says "Subset-cardinality (T3) — W10." Verify all world cross-references are accurate against the plan.

**Why**: Inaccurate cross-references damage the transfer layer. If the learner looks back and the referenced world does not match where the skill was actually taught, the retrieval link is broken. This is a small accuracy issue but matters for a pset world whose purpose is retrieval.

**Where**: L08 conclusion

**Effort**: Low (verify and correct any wrong references)

**Recommend**: Yes

---

### 10. No level exercises `Finset.sdiff` (set difference) — a gap given the boss uses it

**What**: Add a standalone pset level that requires set-difference reasoning (not just membership *in* a set difference, but proving an identity or subset involving `\`).

**Why**: The boss (L08, Part 1) uses `Finset.mem_sdiff`, but no earlier pset level exercises set difference. The learner encounters `sdiff` for the first time in the boss, which undermines the pset's purpose of retrieval under reduced scaffolding. Either add a level that retrieves `sdiff` before the boss, or restructure L03 to be a `sdiff`-based identity instead of the absorption law (since absorption uses only `\cap` and `\cup`, which are already exercised by other levels).

**Where**: New level before L08, or rework L03

**Effort**: Medium (new or reworked level)

**Recommend**: Consider

---

## Overall impression

The world has solid structural bones: it sequences through membership, subset, set operations, filter+card, induction, and transfer before closing with an integrative boss, which matches the pset pattern well. The two transfer levels (L06, L07) have excellent conclusions that genuinely bridge Lean and paper reasoning — these are among the strongest transfer moments in the course so far and should not be changed.

The single most important improvement is **replacing the L05 target with a statement that actually requires finset induction** (suggestion 1). A pset level whose model solution is `omega` regardless of the tactic used is not testing retrieval of finset induction — it is testing whether the learner remembers that `omega` closes arithmetic goals. This undermines the world's core promise. Closely behind that: the L06 and L07 proofs are too thin for a pset (one `exact` and one `exact` respectively), and the boss decomposes into independent parts rather than requiring genuine multi-step integration. Addressing these would transform the world from "light practice on new numbers" to "genuine retrieval under reduced scaffolding," which is what the plan promises.
