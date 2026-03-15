# W4 MultisetHierarchy -- Enrichment Review (Round 1)

## Ranked suggestions

### 1. Add a "Multiset.count" level that exercises rewriting, not just `decide`

**What**: L04 (MultisetDuplicates) introduces `Multiset.count` but solves the proof with `decide`. Add a level (or modify L04) where the learner proves a count identity using a rewrite lemma like `Multiset.count_cons_self` or `Multiset.count_cons_of_ne` rather than computation.

**Why**: `Multiset.count` is presented as a concept ("here is how you count occurrences") but the learner never actually *reasons* about it -- they just ask the kernel to compute. This means the proof-move layer is empty for this concept. Counting with multiplicity is the central distinguishing feature of multisets, and the learner should internalize the recursive structure: "count increments when the element matches, stays the same otherwise." This is exactly what `count_cons_self` and `count_cons_of_ne` teach. Without this, the learner has seen `Multiset.count` but has no proof move for reasoning about it symbolically -- which is the only form that transfers to non-concrete situations.

**Where**: New level between current L04 and L05, or modify L04 to be two-part: first a concrete `decide` exercise, then a symbolic rewrite exercise.

**Effort**: High (new level)

**Recommend**: Yes

---

### 2. Add a level proving that two different lists give the same multiset but different lists

**What**: Add a level where the learner proves something like `(↑[1, 2, 3] : Multiset Nat) = ↑[3, 1, 2]` (already in L02) AND `[1, 2, 3] ≠ [3, 1, 2]` (not currently anywhere). Better yet, prove the conjunction: "these lists give the same multiset, but the lists are not equal."

**Why**: The world's central narrative is *information loss*. But information loss is only visceral when you demonstrate that two things that are distinguishable at the lower level become indistinguishable at the higher level. L02 shows the "same multiset" half, and L06 shows the analogous fact for finsets. But the world never makes the learner prove that the two original lists are actually *different* -- which is the "before" that makes the "after" meaningful. This is a missed teaching moment. In L02, the learner proves `↑[1,2,3] = ↑[3,1,2]` and is told "order doesn't matter," but never proves `[1,2,3] ≠ [3,1,2]` (which is the reason this is interesting). Without the negative half, the learner is told about information loss rather than experiencing it.

**Where**: Modify L02 to be a conjunction: `[1, 2, 3] ≠ [3, 1, 2] ∧ (↑[1,2,3] : Multiset Nat) = ↑[3,1,2]`. Or add a new level after L02.

**Effort**: Medium (modify existing level or add a short new one)

**Recommend**: Yes

---

### 3. Add a level that shows `Multiset.card_toFinset_le` (or derives the inequality)

**What**: Add a level where the learner proves `(↑l).toFinset.card ≤ (↑l).card` for a specific list with duplicates, using a general lemma rather than `decide`.

**Why**: L07 (ThreeLayers) mentions in its conclusion that `(↑l).toFinset.card ≤ (↑l).card = l.length` and says "Equality holds exactly when the list has no duplicates." But this general fact is never proved -- it is only asserted in prose. The learner verifies a specific instance (card 3 vs card 4 for `[1,2,1,3]`) by `decide`, but never sees the general inequality as a lemma. Proving the inequality for a general multiset (even just applying the existing mathlib lemma `Multiset.toFinset_card_le_card` or `Multiset.card_toFinset_le_card`) would teach the learner that the specific numerical example they computed in L07 is an instance of a general principle. This is a missed "derivable result" -- the specific example in L07 is a consequence of the general lemma, and showing the derivation is more instructive than showing the instance.

**Where**: New level after L07, or modify L07 to include a third part.

**Effort**: Medium (new level or extend existing)

**Recommend**: Yes

---

### 4. Connect `Multiset.Nodup` back to `List.Nodup` from W3

**What**: In L08 (DedupAndToFinset), the world introduces `Multiset.Nodup` but never connects it back to `List.Nodup` from W3 L09. Add a sentence or sublevel that demonstrates: when you coerce a `Nodup` list to a multiset, the multiset is also `Nodup` (i.e., `l.Nodup → (↑l : Multiset α).Nodup`). This could also be a level proving that `List.toFinset l = Multiset.toFinset (↑l)` -- making the shortcut from L06 non-mysterious.

**Why**: W3 L09 carefully taught `List.Nodup` and the conclusion said "a list satisfying `Nodup` can be converted to a finset without losing information." W4 L08 introduces `Multiset.Nodup` as if it were a new concept. But `Multiset.Nodup` *is* `List.Nodup` -- the multiset version is just the quotient-lifted version of the list version. Making this connection explicit rewards the learner for their work in W3 and demonstrates that the quotient doesn't break the property. Without this connection, the learner might think `List.Nodup` and `Multiset.Nodup` are unrelated, which is a misconception.

**Where**: Extend L08 or add a new level between L08 and L09. Even a paragraph in L08's conclusion connecting the two would help.

**Effort**: Low (conclusion text) to Medium (new sublevel)

**Recommend**: Yes

---

### 5. Unnamed proof strategy: the "reduce-then-compute" pattern

**What**: Multiple levels in this world use the same two-step proof pattern: (1) rewrite with a structural lemma to reduce the goal to a simpler form, then (2) close with `decide` or `rfl`. This pattern appears in L02 (`rw [coe_eq_coe]; decide`), L03 (`rw [card_map]; rfl`), L08 (`exact toFinset_val _`), and the boss. Name this pattern explicitly.

**Why**: This is a legitimate proof strategy: "use a structural lemma to convert a derived-type question into a base-type question, then compute." The learner uses it repeatedly but it is never articulated as a reusable technique. In later worlds (W5-W9), the learner will encounter similar patterns with finset lemmas (rewrite membership into a simpler proposition, then close). Naming it now ("reduce-then-compute") gives the learner a handle to recognize when to apply it. The introduction or conclusion of L02 or L03 is the natural place.

**Where**: Add a "Proof move" note in the conclusion of L02 or L03 (or both) that names this strategy.

**Effort**: Low (a paragraph in an existing conclusion)

**Recommend**: Yes

---

### 6. Add `Multiset.mem` and show how membership differs across the hierarchy

**What**: The world never introduces `Multiset.mem` or `∈` for multisets. Add a level where the learner proves `1 ∈ (↑[1, 2, 3] : Multiset Nat)` and contrasts it with `List.mem` and `Finset.mem`.

**Why**: Membership is the most fundamental operation on any collection type, and the world omits it entirely for multisets. The learner saw `List.mem` in W3 and will see `Finset.mem` in W6, but `Multiset.mem` is skipped. This is a gap in the "three lenses on the same data" narrative. Without it, the learner cannot reason about what "is in the multiset" means. Additionally, the relationship `a ∈ (↑l : Multiset α) ↔ a ∈ l` (via `Multiset.mem_coe`) is a natural complement to `Multiset.coe_eq_coe` from L02 -- both are about the bridge between lists and multisets, and they form a pair (equality vs membership).

**Where**: New level, ideally early in the world (after L01 or L02).

**Effort**: High (new level)

**Recommend**: Yes

---

### 7. The boss should require at least one non-`decide` step beyond `constructor`

**What**: The boss (L09) is a four-part conjunction where every part is closed by `rfl` or `decide`, with `constructor` as the only structural tactic. Consider making at least one conjunct require a rewrite step (e.g., proving `m.card = (↑[1, 2, 1, 3, 2]).card` for a different representation of the same multiset, requiring `coe_eq_coe`).

**Why**: A boss level should integrate the proof moves taught in the world, not just the definitions. The current boss tests whether the learner can use `constructor` (from W1), `rfl` (from W1), and `decide` (from W2). It does not test any proof move specific to W4: no `coe_eq_coe` rewriting, no `card_map`, no `toFinset_val`, no `count_cons` reasoning. The boss is effectively a computation check, not a proof integration exercise. The plan says the boss should test "Integration of M16--M20, C3, C4," but the proof does not integrate anything -- it delegates everything to the kernel.

**Where**: Modify L09 to include at least one conjunct that requires `rw [Multiset.coe_eq_coe]` or a similar structural rewrite.

**Effort**: Medium (modify boss statement and proof)

**Recommend**: Yes

---

### 8. Add foreshadowing for `Finset.filter` and `Finset.image` in the Multiset.map level

**What**: In L03 (MultisetOperations), mention in the conclusion that `Multiset.map` has a finset analogue (`Finset.image`) that will appear in W8, and that the cardinality preservation story becomes more nuanced for `Finset.image` (because deduplication after mapping can shrink the result).

**Why**: `Multiset.map` preserves cardinality unconditionally (`card_map`), but `Finset.image` does not -- because mapping can create duplicates that are then removed. This is a subtle point that will confuse learners in W8 if they expect `Finset.image` to behave like `Multiset.map`. A one-sentence foreshadowing in L03's conclusion ("In finsets, mapping can change cardinality because duplicates created by the function are removed -- you will see this in a later world") prepares the learner and reinforces the hierarchy's central theme: finsets lose multiplicity information.

**Where**: Add 1-2 sentences to L03's conclusion.

**Effort**: Low (conclusion text)

**Recommend**: Consider

---

### 9. Add a "What if" level: what happens when you apply `toFinset` to an already-duplicate-free multiset?

**What**: Add a level where the learner proves that for a `Nodup` multiset, `toFinset` preserves cardinality: `m.Nodup → m.toFinset.card = m.card`. Or at minimum, demonstrate on a concrete example that `[1, 2, 3].toFinset.card = [1, 2, 3].length` (no information loss because there were no duplicates to begin with).

**Why**: The world emphasizes that `toFinset` removes duplicates and loses information. But it never asks the learner to think about *when* information is preserved. The answer -- "when the multiset already has no duplicates" -- connects `Nodup` (from W3) to `toFinset` (from this world) and closes the conceptual loop. This is exactly the kind of "boundary case" level that builds mathematical maturity: after seeing the general case (information is lost), examine when the loss is zero.

**Where**: New level after L06 or L07.

**Effort**: High (new level)

**Recommend**: Consider

---

### 10. Vocabulary seeding: mention `Multiset.filter` in passing

**What**: `Multiset.filter` is listed as a coverage item (M19) and will be needed in later worlds, but it is never mentioned in W4. Add a sentence in L03's conclusion or introduction noting that `Multiset.filter` exists (analogous to `List.filter` from W3) and will be used later.

**Why**: The plan lists `Multiset.filter` as part of M19, and L03 is the natural place to seed it since L03 already covers `Multiset.card` and `Multiset.map`. A single sentence ("Multisets also support `Multiset.filter`, analogous to `List.filter` -- you will use it in a later world") costs nothing and prevents the learner from being surprised when `Multiset.filter` appears without introduction.

**Where**: L03 conclusion, one sentence.

**Effort**: Low (one sentence)

**Recommend**: Consider

---

### 11. The conclusion of L01 should mention that `Multiset.card` on a coerced list is not just "equal to" but "definitionally equal to" `List.length`

**What**: L01's conclusion says "the cardinality is preserved" but the proof is `rfl`, which means the equality is *definitional*. The conclusion should explicitly note this: "This is not just a theorem -- it is a definitional equality, which is why `rfl` works."

**Why**: The distinction between definitional equality (provable by `rfl`) and propositional equality (requiring `rw` or other tactics) is a fundamental Lean concept that the learner will need throughout the course. L01 is a good moment to reinforce it because the proof is `rfl` and the learner might wonder why. The conclusion mentions `rfl` but does not explain *why* it works. A one-sentence clarification would teach a transferable Lean concept.

**Where**: L01 conclusion, modify existing text.

**Effort**: Low (one sentence)

**Recommend**: Consider

---

## Overall impression

The world has a clear narrative arc -- List to Multiset to Finset, with information loss at each step -- and the progression of levels follows a logical order. The introduction and conclusion texts are well-written and include good "plain language" summaries and the comparison table in L04 is excellent. The world does a good job of covering the key definitions (`Multiset`, `Multiset.card`, `Multiset.map`, `Multiset.count`, `Multiset.toFinset`, `Multiset.dedup`, `Multiset.Nodup`) and the `coe_eq_coe` bridge lemma.

The single most important improvement is **adding proof-move depth**. Currently, every level in the world is closed by `rfl`, `decide`, `exact`, or `constructor` -- tactics that were all introduced in earlier worlds. The world introduces many new *definitions* but teaches zero new *proof moves*. The learner exits this world knowing what multisets are and what operations exist, but they have not learned how to *reason* about multisets beyond asking the kernel to compute. Adding levels that require symbolic reasoning with `count_cons_self`/`count_cons_of_ne`, `mem_coe`, or `card_toFinset_le_card` would transform this from a "definition tour" into a world that teaches transferable proof skills.
