# W9 FinsetCardinality -- Enrichment Review (Round 1)

## Ranked suggestions

### 1. Derivable result: inclusion-exclusion as a corollary of the disjoint-union case

**What**: Add a level (between current L07 and L08, or as a two-part L07) that first proves the disjoint case `Disjoint s t -> (s ∪ t).card = s.card + t.card` using `Finset.card_union_of_disjoint`, and then derives inclusion-exclusion from it (or at least discusses how the general formula specializes).

**Why**: The world currently presents `card_union_add_card_inter` as an atomic fact. But the disjoint case (`|s ∪ t| = |s| + |t|` when `s ∩ t = ∅`) is both simpler and more intuitive. It is the "obvious" case that every learner expects, and the general inclusion-exclusion formula is the correction for when disjointness fails. Presenting the disjoint case first gives the learner a base intuition, and then inclusion-exclusion becomes "what happens when the sets overlap" rather than an opaque identity. This is a genuine mathematical depth issue: a derivable special case is being skipped in favor of the general formula, and the conceptual relationship between them is lost.

**Where**: New level between L07 and L08 (renumber L08/L09 to L09/L10), or split L07 into two levels (L07a: disjoint union, L07b: general inclusion-exclusion).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. Missing concrete verification after inclusion-exclusion

**What**: After L07 proves the inclusion-exclusion identity via `exact Finset.card_union_add_card_inter _ _`, add a follow-up part (or a separate level) that makes the learner actually compute the numerical values. The current L07 statement is `(s ∪ t).card + (s ∩ t).card = s.card + t.card`, which Lean verifies structurally without the learner ever seeing the numbers 4, 2, 3, 3.

**Why**: The conclusion text says "4 + 2 = 6 = 3 + 3" and walks through the computation, but the learner never performed it. The proof was a single `exact`. This is an example-layer gap: the concrete example is described in prose but never forced through the learner's hands. A level that asks the learner to prove `(({1,2,3} : Finset Nat) ∪ {2,3,4}).card = 4` (or the full `4 + 2 = 3 + 3` numerically) would require the learner to combine inclusion-exclusion with actual cardinality computation (rewriting with `card_insert_of_notMem`, `card_singleton`, etc.), integrating the skills from L01-L04 with L07.

**Where**: New level after L07 or as a second part of L07.

**Effort**: High (new level) or medium (second conjunct in L07).

**Recommend**: Yes.

---

### 3. `simp` is not disabled -- potential exploit on every level

**What**: `simp` (without `simp_all`) is still available. In many of these levels, `simp` alone (or `simp [Finset.card_empty]`, `simp [Finset.card_singleton]`, etc.) may close the goal, bypassing the intended lemma application. Verify whether `simp` closes any of L01-L09 and, if so, add `simp` to `DisabledTactic` for those levels.

**Why**: The standard disabled set for this course is `trivial decide native_decide simp aesop simp_all`. This world uses `trivial decide native_decide aesop simp_all` but omits `simp`. If `simp` closes `(∅ : Finset Nat).card = 0` or `({42} : Finset Nat).card = 1`, the learner can bypass the lesson entirely. This is the same category of exploit that was caught and fixed in earlier worlds (W1-W4).

**Where**: All levels (L01-L09).

**Effort**: Low (add `simp` to each `DisabledTactic` line).

**Recommend**: Yes.

---

### 4. No multi-step cardinality computation level

**What**: Add a level where the learner must compute the cardinality of a literal finset from scratch, chaining `card_insert_of_notMem` and `card_singleton` (and possibly `card_empty`), rather than applying a single lemma. For example: prove `({1, 2, 3} : Finset Nat).card = 3` by peeling off inserts one at a time.

**Why**: L03 in the conclusion text describes the "peel off each insert" proof pattern as the standard technique for computing cardinalities of literal finsets, but the learner never actually performs this pattern. L03 applies `card_insert_of_notMem` once in an abstract setting; no level requires chaining it. The boss (L09) uses only single-lemma applications (`card_range`, `card_union_add_card_inter`, `card_filter_le`). The advertised "pattern" is never exercised, which means it is not actually taught. This is a proof-move layer gap.

**Where**: New level between L04 and L05, or replace part of the boss with this challenge.

**Effort**: High (new level) or medium (modify boss).

**Recommend**: Yes.

---

### 5. The boss level is too easy -- no integration of proof moves

**What**: Restructure the boss (L09) so that at least one part requires genuine multi-step reasoning rather than a single `exact` or `rw`. Currently all three parts are single-lemma applications: `exact Finset.card_range 10`, `exact Finset.card_union_add_card_inter _ _`, `exact Finset.card_filter_le _ _`. The boss tests "can you pick the right lemma from a menu" but not "can you combine lemmas to prove something new."

**Why**: A boss level should require integration. The current boss is three independent retrieval exercises bundled into a conjunction. Each part is identical in difficulty to the level that introduced the lemma. A boss that required, say, computing `({1,2,3} ∪ {3,4,5}).card` as a specific number (requiring inclusion-exclusion + concrete cardinality computation) would genuinely integrate the world's content. The current boss would receive a "P2: no integration" flag under the playtest rubric.

**Where**: L09 (modify in place).

**Effort**: Medium (rewrite boss statement and proof).

**Recommend**: Yes.

---

### 6. `card_insert_of_notMem` non-membership proof is trivially provided in L03

**What**: In L03, the non-membership hypothesis `h : a ∉ s` is given as a premise. The learner just feeds it to the lemma. Consider a variant (or second part) where the learner must *derive* the non-membership proof from concrete data, e.g., prove `3 ∉ ({1, 2} : Finset Nat)` and then apply `card_insert_of_notMem`.

**Why**: In real use, `card_insert_of_notMem` requires you to prove `a ∉ s` yourself. If the hypothesis is always handed to the learner, they never practice the actual bottleneck of using this lemma. The "peel off inserts" pattern from the conclusion of L03 requires producing non-membership proofs at each step. Without ever practicing that, the pattern remains theoretical.

**Where**: L03 (add a second part) or new level after L03.

**Effort**: Medium (modify L03) or high (new level).

**Recommend**: Yes.

---

### 7. Missing connection to `Finset.card_pos` and nonemptiness

**What**: Mention (in a conclusion or as a brief aside) that `Finset.card_pos` connects cardinality to nonemptiness: `0 < s.card ↔ s.Nonempty`. This connects cardinality back to the structural concept of nonemptiness.

**Why**: The world builds a toolkit of cardinality lemmas but never connects cardinality to existence. The fact that "card > 0 implies nonempty" is an important bridge between counting and logic. It foreshadows `V9` (contradiction via cardinality) from the proof-move map, which appears in W12. A single sentence in the L01 or L02 conclusion ("Notice: if `s.card > 0`, then `s` must contain at least one element -- this is `Finset.card_pos`") would seed this connection at zero cost.

**Where**: L01 or L02 conclusion.

**Effort**: Low (a sentence in a conclusion).

**Recommend**: Consider.

---

### 8. No foreshadowing of `Finset.card_image_of_injective`

**What**: In the conclusion of L08 or L09, mention that `Finset.card_image_of_injective` gives `(s.image f).card = s.card` when `f` is injective. This connects cardinality to the image operation from W8.

**Why**: The learner has already seen in W8_ex (L04) that the image under squaring preserves cardinality because squaring is injective on `{1,2,3,4,5}`. The general principle -- injective functions preserve cardinality -- is a key fact that links the operations world (W8) to the cardinality world (W9). Mentioning it explicitly closes a conceptual loop and seeds vocabulary for when it appears formally later. It also connects to W8 L07 ("image can shrink cardinality"), giving the exact condition under which it doesn't shrink.

**Where**: L08 or L09 conclusion.

**Effort**: Low (a sentence or two in a conclusion).

**Recommend**: Consider.

---

### 9. The world intro (L01) claims `card_singleton` and `card_insert_of_notMem` were seen "in passing" -- verify accuracy

**What**: L01's introduction says "You have already seen `Finset.card` in passing -- you used `card_singleton` and `card_insert_of_notMem` to compute the size of literal finsets." Verify this is accurate: did W5, W6, W7, W8, or W8_ex actually use these lemmas? The W8_ex boss does compute cardinalities, but via `rfl` (definitional reduction) or `Finset.card_powerset`/`Finset.card_product`, not via `card_singleton`/`card_insert_of_notMem`. If these lemmas were not previously used, the intro text is misleading and should be corrected.

**Why**: Inaccurate forward references confuse the learner. If the intro promises retrieval of something never taught, the learner will feel lost.

**Where**: L01 introduction text.

**Effort**: Low (text edit).

**Recommend**: Yes.

---

### 10. Missing "What if?" level: what happens when you apply `card_insert_of_notMem` with a false hypothesis?

**What**: Add a brief discussion (in L04's conclusion) about what would happen if you tried to apply `card_insert_of_notMem` when `a ∈ s`. The type system prevents it (you can't provide a proof of `a ∉ s`), but the learner should understand *why* the lemma has the hypothesis: without it, the conclusion `(insert a s).card = s.card + 1` would be false.

**Why**: L04 already sets up the contrast (mem vs notMem), but it presents L03 and L04 as parallel facts rather than explaining that L03's hypothesis is *necessary*. The learner could leave thinking both lemmas are equally applicable to any finset, rather than understanding that the hypothesis `a ∉ s` is the crux. A sentence like "If you could apply `card_insert_of_notMem` without the non-membership proof, you would 'prove' that `{1,1}.card = 2` -- but finsets have no duplicates, so `{1,1} = {1}` and the cardinality is 1" would crystallize why the hypothesis matters.

**Where**: L04 conclusion.

**Effort**: Low (a few sentences in the conclusion).

**Recommend**: Consider.

---

### 11. Cross-world foreshadowing: `Finset.induction_on` in W10

**What**: The L09 conclusion mentions W10 (Finset induction) and says "proving properties of all finsets by building them up from `∅` one `insert` at a time." This is good, but could be strengthened by connecting it to the specific cardinality lemmas from this world: "The three lemmas `card_empty`, `card_singleton`, and `card_insert_of_notMem` mirror the base case and inductive step of `Finset.induction_on`. In the next world, you will see that this is not a coincidence."

**Where**: L09 conclusion.

**Effort**: Low (a sentence).

**Recommend**: Consider.

---

## Overall impression

The world has a clean structure: it introduces cardinality lemmas in a logical order (empty, singleton, insert-new, insert-dup, range, range-zero, inclusion-exclusion, filter-bound) and has good prose that explains both the Lean and mathematical content. The transfer moment for inclusion-exclusion is well-placed, and the contrast between L03 and L04 (insert-new vs insert-dup) is a solid pedagogical move. The world's narrative arc -- from base cases through combination tools to a boss -- is coherent.

The single most important improvement is that **the world is too shallow in its demands on the learner**. Every level is a single-lemma application (`rw` or `exact` with one lemma). No level requires chaining lemmas, producing non-membership proofs, or performing a genuine multi-step computation. The "peel off inserts" pattern described in L03's conclusion is never exercised. The boss tests lemma recognition, not integration. Adding a multi-step cardinality computation level (suggestion 4) and restructuring the boss to require genuine integration (suggestion 5) would transform this from a lemma catalog into a world that builds real proof fluency. The disjoint-union level (suggestion 1) and the `simp` disable (suggestion 3) are also high-priority fixes.
