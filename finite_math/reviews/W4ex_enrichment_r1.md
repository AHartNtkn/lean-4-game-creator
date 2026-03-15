# W4_ex ListUnderLenses -- Enrichment Review (Round 1)

**World**: ListUnderLenses (5 levels)
**Type**: Example world (concretizes W4 MultisetHierarchy)
**Concrete object**: The list `[1, 2, 1, 3]`
**Reviewer**: Enrichment reviewer, fresh context

---

## Ranked suggestions

### 1. Add a `Multiset.count` level to make the multiplicity loss tangible

**What**: Add a level (between current L02 and L03) where the learner proves `Multiset.count 1 (↑[1, 2, 1, 3]) = 2` and then shows that in the finset, `1` appears "once" (i.e., there is no `count` -- only membership). This directly instantiates the "what does each lens see?" question with the most important distinguishing operation.

**Why**: The world claims to show what each lens keeps and discards, but it never exercises `Multiset.count` -- the single operation that most vividly distinguishes multisets from finsets. W4 L06 introduced `Multiset.count` and the learner used it there on exactly this list. The example world should revisit it, because the *contrast* between "count = 2 as a multiset" and "just a member as a finset" is the whole point of the hierarchy. Without this level, the cardinality difference (4 vs 3) is the only signal that duplicates matter, and it is indirect.

**Where**: New level between L02 and L03 (becomes L03; current L03-L05 shift to L04-L06).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. Add a `List.toFinset` shortcut level to connect to W4 L09

**What**: Add a level where the learner proves `([1, 2, 1, 3] : List Nat).toFinset = {1, 2, 3}` using `List.toFinset` directly (not going through the multiset intermediate). Then prove this equals the result of the two-step pipeline (`Multiset.toFinset (↑[1, 2, 1, 3])`).

**Why**: W4 L09 introduced `List.toFinset` as a shortcut that combines both hierarchy steps. The current world never uses it -- it always goes through the explicit `↑` then `.toFinset` path. The example world is the natural place to show that the shortcut and the explicit pipeline produce the same result. This reinforces the `List.toFinset` API and the mental model that the two paths are equivalent. It also provides a natural place for a `rfl` or `decide` proof that connects the two spellings.

**Where**: New level after the finset perspective (current L03), or as part of the boss.

**Effort**: Medium (could be folded into the boss as an additional conjunct, or a standalone level).

**Recommend**: Yes.

---

### 3. The L05 boss's transfer moment is in the conclusion, not in a proof

**What**: The plan calls for L05 to be a "Transfer" level where the learner "states in plain English why |{1,2,3}| = 3 even though the list has 4 elements." The current implementation puts the transfer moment entirely in the L05 *conclusion* text, but the L05 *proof* is a four-part conjunction that is purely mechanical (repeating L01-L04 techniques). The transfer content is passive reading, not active work.

**Why**: Transfer is supposed to be a coverage item (T9). Making it purely textual means the learner can skip-read it. The W3_ex world (FinThreeExamples) handles transfer similarly (L06 had a computationally trivial proof with transfer in the conclusion), but that world had 11 levels of substantive work before the transfer. Here, with only 5 levels, the transfer moment carries more weight and deserves a level where the learner does something that cannot be done with `decide` alone -- for example, proving that `([1, 2, 1, 3] : List Nat).toFinset.card < ([1, 2, 1, 3] : List Nat).length` (strict inequality, not just `le`), which makes the information loss concrete and requires applying `toFinset_card_le` plus showing the inequality is strict.

**Where**: Modify L05 or add a dedicated transfer level.

**Effort**: Medium (redesign the boss or add a new level).

**Recommend**: Yes.

---

### 4. The world never exercises `Finset.mem` on the finset

**What**: L03 proves `toFinset = {1, 2, 3}` and `card = 3`, but never proves `2 ∈ ([1,2,1,3] : List Nat).toFinset` (membership in the finset). Both L01 and L02 prove membership (`2 ∈ list`, `2 ∈ multiset`), creating a pattern that L03 breaks. The three-lens comparison would be more symmetric if L03 also includes a membership proof.

**Why**: The world's narrative is "same data, three lenses, compare what you see." L01 and L02 each prove both cardinality and membership. L03 proves cardinality and equality-to-a-literal but not membership. Adding `2 ∈ toFinset` to L03 completes the parallel structure and lets the conclusion show a clean three-row comparison: "membership holds in all three, cardinality drops from 4 to 3." The proof is trivial (`decide`), but the symmetry matters for the learner's mental model.

**Where**: Modify L03 to add `2 ∈ ...toFinset` as a third conjunct.

**Effort**: Low (add one conjunct and its hint).

**Recommend**: Yes.

---

### 5. No level exercises non-membership or the failure of `count`

**What**: Add a level or conjunct showing `4 ∉ ([1, 2, 1, 3] : List Nat)` (non-membership). Alternatively, show `Multiset.count 4 (↑[1, 2, 1, 3]) = 0` (an element not in the collection).

**Why**: The world only exercises positive membership. A learner might not realize that membership is decidable in all three representations (and that non-membership is also provable by `decide`). Non-membership is a natural "what if?" moment: "what about an element that is NOT in the list?" This is especially valuable because W6 (Membership) will teach non-membership (`4 ∉ {1,2,3}`), and previewing it here in the example world provides continuity. It also completes the picture: the element `4` is absent from the list, the multiset, and the finset -- uniformly.

**Where**: Could be a conjunct in L01 or L02, or part of the count level (suggestion 1).

**Effort**: Low (add a conjunct).

**Recommend**: Consider.

---

### 6. The reduce-then-compute pattern name is used but never explicitly called back

**What**: L04 says "This is the reduce-then-compute pattern you practiced in W4" in the introduction, and the conclusion says "The reduce-then-compute pattern from W4." But the world never explicitly names the two steps (reduce, compute) in the hints the way W4 L13 does. The hints just say "use this lemma, then decide."

**Why**: The example world is a reinforcement opportunity. If the world is going to invoke the pattern name, it should do so in a way that the learner can recognize and apply. The L04 hints should label the steps: "Step 1 (Reduce): `rw [Multiset.coe_eq_coe]`" and "Step 2 (Compute): `decide`." This costs almost nothing (a few words in the hint text) but makes the pattern retrieval explicit rather than implicit.

**Where**: L02 (the `rw [Multiset.mem_coe]; decide` proof) and L04 (the `rw [coe_eq_coe]; decide` proof).

**Effort**: Low (modify hint text).

**Recommend**: Yes.

---

### 7. The world does not exercise `Multiset.count_coe_perm` or show that count is permutation-invariant

**What**: In L04, the conclusion mentions "Count: same (count 1 = 2 in both)" but this is never proved. The learner is told that reordering preserves count but never verifies it.

**Why**: This is a "stated but unproved" claim. The conclusion of L04 lists five things that do not change under reordering (multiset, finset, cardinality, membership, count) but only proves one (multiset equality). The others are consequences, but at least one should be exercised. A conjunct like `Multiset.count 1 (↑[1, 2, 1, 3]) = Multiset.count 1 (↑[3, 1, 2, 1])` would cost the learner only `rfl` (since the multisets are equal) or `decide`, but it would make the "count is invariant" claim concrete. This connects directly to suggestion 1 (the count level).

**Where**: L04, as an additional conjunct.

**Effort**: Low-Medium (add a conjunct to L04).

**Recommend**: Consider.

---

### 8. The boss does not feel like a boss -- it is purely a concatenation of earlier proofs

**What**: The boss (L05) is a four-part conjunction where each part exactly recapitulates a technique from L01-L04. There is no synthesis, no new combination, and no moment where the learner must choose which technique to apply. The fourth part (`toFinset_card_le`) is the only non-trivial element, and it was already used in W4 L11.

**Why**: Compare with the W3_ex boss (L11), which required combining injectivity and surjectivity into bijectivity -- a genuine synthesis. Or the W4 boss (L14), which combined `card_map`, `map_coe + coe_eq_coe`, and `toFinset_card_le` on a *new* multiset (the mapped `↑[0,1,0,2]`), requiring the learner to transfer skills to fresh data. The current boss uses the same list `[1,2,1,3]` that the learner has been working with for four levels. Nothing is new. A better boss would either (a) use a *different* list (e.g., `[2, 3, 2, 3, 1]`) to test transfer, or (b) require a derivation that combines multiple concepts in a way that no single level does (e.g., "prove that the finset cardinality is strictly less than the list length, then explain why").

**Where**: Redesign L05 (or the new final level).

**Effort**: High (redesign the boss).

**Recommend**: Yes.

---

### 9. No foreshadowing of W5 (Constructing Finsets)

**What**: The conclusion of L05 mentions "upcoming worlds" but does not connect to any specific concept from W5. It could seed the idea of `insert` or `{a, b, c}` notation: "You have been writing finsets like `{1, 2, 3}` as literals. In the next world, you will learn what this notation actually means -- it desugars to `insert 1 (insert 2 {3})`."

**Where**: L05 conclusion (or the finset level's conclusion).

**Effort**: Low (one sentence).

**Recommend**: Consider.

---

### 10. The introductions do not distinguish this world from W4 L10

**What**: W4 L10 ("The three-layer hierarchy") already proves the exact same comparison on the exact same list (`[1, 2, 1, 3]`): multiset card = 4, finset card = 3. L01 of the example world essentially re-does L10 of W4 on the same data with the same tactics.

**Why**: An example world should feel distinct from the lecture world. Right now, the first three levels of W4_ex feel like a replay of W4 L10. The world would benefit from an explicit acknowledgment in the L01 introduction: "In W4, you proved these facts in one big conjunction. Here, you will explore each lens *separately*, with more attention to what each representation sees and what it misses." This meta-commentary helps the learner understand why they are revisiting familiar territory and primes them to look for the new insights (count, transfer, invariance).

**Where**: L01 introduction.

**Effort**: Low (a few sentences).

**Recommend**: Consider.

---

## Overall impression

**What the world does well**: The world has a clear narrative arc -- one concrete object examined through three mathematical lenses, with a clean visual comparison table in each conclusion. The proof techniques are well-matched to the pedagogical goals (definitional equality for list/multiset, `decide` for finset computation, bridge lemma + compute for permutation invariance). The ASCII hierarchy diagrams in the conclusions are effective. The "In plain language" sections at the end of each level are well-written and genuinely transfer-oriented. The L04 (reordering invariance) level is the strongest level in the world -- it is the most distinctively "example world" content, showing something that only matters when you have a specific piece of data.

**The single most important improvement**: The world needs a `Multiset.count` level (suggestion 1). The hierarchy's central distinction is multiplicity: multisets have it, finsets do not. But the world never exercises `Multiset.count`, which is the API that makes multiplicity concrete. Without it, the world proves that cardinality drops from 4 to 3 but never shows *why* in terms the learner can touch. Adding a count level -- "the element 1 has count 2 in the multiset, but no count operation exists for finsets; you just have membership" -- would make the hierarchy's information-loss story visceral rather than numerical. This is the "how did we miss that?" improvement.
