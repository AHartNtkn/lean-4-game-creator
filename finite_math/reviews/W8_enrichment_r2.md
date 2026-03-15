# W8 FinsetTransformations — Enrichment Review (Round 2)

## R1 disposition

Before new suggestions, here is the status of each R1 item:

| # | R1 suggestion | Status |
|---|---------------|--------|
| 1 | L07 is a trivial one-liner — rewrite to show actual collision | **Not addressed.** L07 is still `exact Finset.card_image_le`. The level remains an empty-calorie `exact`-and-done exercise. |
| 2 | Add a non-membership-in-image level (false-witness direction) | **Not addressed.** No level asks the learner to prove `b ∉ Finset.image f s`. |
| 3 | Teach `rcases ... with ⟨a, ha, rfl⟩` before the boss | **Not addressed.** The `rfl` substitution pattern still appears for the first time in L08. L04 does not use it. |
| 4 | L05 exercise is identical to L03 — make the learner use `card_map` | **Partially addressed.** L05 now uses `Nat.succ_injective` (standard mathlib embedding) instead of a hand-rolled proof, which is cleaner. However, the exercise is still membership-only (`4 ∈ s.map e`). The learner never uses `card_map` in a proof. The core concern persists. |
| 5 | Dual composition (image then filter) never practiced | **Not addressed.** L06 conclusion still mentions `filter_image` without any exercise. |
| 6 | `simp` not in DisabledTactic despite standard set | **Not addressed.** `simp` is still enabled in all 8 levels. (Tracked as systemic — noting for completeness.) |
| 7 | No empty-filter misconception level | **Not addressed.** |
| 8 | Boss conclusion references "W6/W7" instead of world names | **Not addressed.** L08 line 105 still says "from W6/W7". |
| 9 | "Outside-in" strategy naming could be more prominent | **Not addressed.** |
| 10 | `card_image_of_injective` in NewTheorem but never used | **Not addressed.** L07 still declares `NewTheorem Finset.card_image_of_injective` but no level in the world requires the learner to use it. |

**Summary**: The boss (L08) now includes a cardinality conjunct using `card_image_le`, which is a good structural improvement. L05 now uses `Nat.succ_injective`, which is cleaner. But none of the 10 R1 suggestions were directly implemented. The same gaps remain.

---

## Ranked suggestions (R2)

### 1. L07 is still an `exact`-and-done level that teaches no proof move (R1 #1 — unchanged)

**What**: L07 asks the learner to prove `(image (· % 2) {0,1,2,3}).card ≤ ({0,1,2,3}).card` by typing `exact Finset.card_image_le`. This is the world's only level addressing the cardinality dimension of image, and it requires zero reasoning.

**Why**: The world's promise includes "reason about membership in resulting finsets" and the plan assigns coverage item C4 (non-injective image). A one-line `exact` does not teach reasoning about non-injectivity. The learner should witness the *collision* — two elements mapping to the same output — and see its cardinality consequence. A better statement would be something like `(Finset.image (· % 2) {0, 1, 2, 3}).card = 2` or `(Finset.image (· % 2) {0, 1, 2, 3}).card < ({0, 1, 2, 3}).card`, requiring the learner to compute the actual image and reason about its size. The `exact` version of `card_image_le` can then appear as one step in the boss (L08 Part B already does this).

**Where**: L07 — rewrite the level statement and proof.

**Effort**: Medium.

**Recommend**: Yes.

---

### 2. The `rfl` substitution pattern in `rcases` is still taught for the first time in the boss (R1 #3 — unchanged)

**What**: L08 uses `rcases hx with ⟨a, ha, rfl⟩` as the key technique, but no prior level introduces this pattern. The first time the learner sees `rfl` used as a pattern variable (not as a closing tactic) is inside the most complex proof in the world.

**Why**: The `rfl` pattern in `rcases` is genuinely novel — it triggers substitution of `f a` for `x` everywhere in the goal. This is a different operation from `rfl` as a proof closer. Introducing it in L04 (where the proof is simple enough to focus on this one new idea) would let L08 use it as a known tool. Currently L04's proof uses `constructor` to split and proves `2 ^ 2 + 1 = 5` by `norm_num`, but could equally well have the learner do `rcases` on a hypothesis of the form `∃ a ∈ s, f a = b` with the `rfl` pattern, then close the remaining goal. This would be a natural evolution from L03 (which introduces the existential) to L04 (which teaches the `rfl` shortcut for handling it).

**Where**: L04 — modify the proof to introduce `rcases ... with ⟨a, ha, rfl⟩` (either by adding a second part or restructuring). Alternatively, add a short dedicated level between L04 and L05.

**Effort**: Medium.

**Recommend**: Yes.

---

### 3. `card_image_of_injective` is declared in inventory but never used (R1 #10 — unchanged)

**What**: L07 includes `NewTheorem Finset.card_image_of_injective` but no level in the world asks the learner to apply it. It is a phantom inventory item.

**Why**: Declaring a theorem as `NewTheorem` signals to the learner "you now have this tool." But the learner never wields it. This creates false confidence. The fix depends on how suggestion #1 is handled: if L07 is rewritten to be about computing the actual image size, then `card_image_of_injective` could be used in a companion level (e.g., prove `(Finset.image Nat.succ {1,2,3}).card = 3` using `card_image_of_injective` and `Nat.succ_injective`). This would connect L05's embedding discussion with L07's cardinality discussion. If no level will use it, remove it from `NewTheorem` and mention it only in the conclusion text.

**Where**: L07 or a new level near L07.

**Effort**: Low (remove from NewTheorem) or medium (add a level that uses it).

**Recommend**: Yes.

---

### 4. L05 exercise is still membership-only — the `map`-vs-`image` distinction is read, not practiced (R1 #4 — unchanged)

**What**: L05's exercise proves `4 ∈ s.map e`, which uses `mem_map` in the exact same pattern as L03/L04's `mem_image`. The introduction discusses `card_map` as the key distinction, but the proof never uses it.

**Why**: The pedagogical justification for L05's existence is the distinction between `map` and `image`. The introduction presents it clearly (table comparing cardinality guarantees), but the exercise asks for the one thing that is *identical* between the two operations. The learner does the same proof shape as L03 and walks away without practicing the thing that makes `map` special. A stronger exercise would have the learner prove `(s.map e).card = s.card` for a specific finset and embedding (using `exact Finset.card_map`), or better yet, prove both membership and cardinality in a two-part statement, so the exercise actually demonstrates the guarantee.

**Where**: L05 — add a second conjunct or modify the statement.

**Effort**: Medium.

**Recommend**: Yes.

---

### 5. No non-membership-in-image level (R1 #2 — unchanged)

**What**: No level asks the learner to prove `b ∉ Finset.image f s`, which requires showing no witness exists.

**Why**: L02 teaches the negative direction for filter (show the conjunction fails). But the negative direction for image — showing that no element of the source maps to the target — is fundamentally different and harder. It requires a universally-quantified argument (for all `a ∈ s`, `f a ≠ b`), which is a different proof shape from providing a single witness. The filter/image parallel is currently asymmetric: both directions for filter, only positive for image. A level like `7 ∉ Finset.image (· * 2) {1, 2, 3}` (requiring exhaustive case analysis on elements of `{1, 2, 3}`) would complete the parallel and introduce a new proof move.

**Where**: New level between L04 and L05.

**Effort**: High (new level).

**Recommend**: Yes.

---

### 6. Boss conclusion still references "W6/W7" instead of world names (R1 #8 — unchanged)

**What**: L08 line 105 says "from W6/W7". The learner does not know internal world numbers.

**Why**: Cross-references should use world names that the learner recognizes from the game UI (e.g., "the FinsetOperations world" or "the Membership world"). Using numeric codes that only the author knows is a usability issue.

**Where**: L08, line 105.

**Effort**: Low (text edit).

**Recommend**: Yes.

---

### 7. The "outside-in" strategy deserves a more prominent naming moment (R1 #9 — unchanged)

**What**: L06's conclusion introduces the "outside-in" strategy for nested finset operations but buries it in the flow of the conclusion text.

**Why**: This is a genuine named proof move that generalizes beyond filter/image to any nested finset expression. It applies retroactively to W7 (combining operations) and forward to W8_ex and W9. A one-sentence callout ("**Strategy: outside-in**. When proving membership in a nested finset expression, always start with the outermost operation's membership lemma.") would make this more memorable and referenceable. The boss (L08) could then say "Apply the outside-in strategy from L06" in its first hint, reinforcing the name.

**Where**: L06 conclusion (rewrite for prominence) and L08 first hint (reference by name).

**Effort**: Low (text edits in two places).

**Recommend**: Consider.

---

### 8. L04's conclusion foreshadows image shrinking but doesn't name the concept — connect to L07 explicitly

**What**: L04's conclusion says "Finset.image can produce finsets that are smaller than the source — because the function might send two different inputs to the same output." This is exactly the concept L07 teaches, but L04 does not name the concept ("non-injectivity" or "collisions") or reference L07.

**Why**: This is a missed foreshadowing connection. L04's conclusion introduces the *idea* of shrinking but in vague terms ("might send two different inputs to the same output"). If it named the concept ("when `f` is **not injective**, some outputs collide") it would seed the vocabulary that L07 needs. This costs one sentence and would make L07's introduction less of a cold start.

**Where**: L04 conclusion — add one sentence naming injectivity.

**Effort**: Low (one sentence).

**Recommend**: Consider.

---

## New observations (not in R1)

### 9. The boss (L08) Part B is still a one-liner `exact Finset.card_image_le` — both cardinality exercises in the world are trivial

**What**: L08's Part B is `exact Finset.card_image_le`, which is the same one-liner as L07. The boss now integrates cardinality *structurally* (via `constructor` and a conjunction), but the cardinality reasoning itself is still zero-effort.

**Why**: Having the boss include a cardinality conjunct was a good change — it means the boss tests both membership and cardinality. But if L07 is rewritten (per suggestion #1) to require actual cardinality computation, the boss's Part B should remain as-is (a quick application of the general lemma) since the boss's complexity comes from Part A. The concern is that *if L07 is not rewritten*, both the world's cardinality exercises are trivial. This suggestion is contingent: if suggestion #1 is implemented, this is not a problem. If #1 is not implemented, then Part B should be strengthened to require computation.

**Where**: L08 Part B — conditional on suggestion #1.

**Effort**: Low (contingent).

**Recommend**: Consider (only if suggestion #1 is rejected).

---

### 10. No level in the world uses `refine` — but the boss's Part A proof shape would benefit from it

**What**: The boss's Part A proof involves constructing a membership in a filtered finset, which requires both membership and predicate. The current proof uses `constructor` then handles each branch. An alternative approach using `refine ⟨?_, ?_⟩` or `refine (Finset.mem_filter.mpr ⟨?_, ?_⟩)` would expose the learner to `refine` as a tool for structured goal construction.

**Why**: `refine` is a fundamental tactic that will be increasingly important in later worlds. The boss's Part A is a natural place to mention it as an alternative (not necessarily to require it). A hint saying "You could also use `refine` to construct the pair directly" would seed the vocabulary without changing the required proof path. This is a lightweight foreshadowing opportunity.

**Where**: L08 Part A — add an alternative hint mentioning `refine`.

**Effort**: Low (one hint).

**Recommend**: Consider.

---

## Overall impression

The world's arc is structurally sound: filter membership (L01-L02), image membership (L03-L04), map as variant (L05), composition (L06), cardinality (L07), boss integration (L08). The introduction texts are clear and well-organized. The comparison tables (filter vs. image in L03's conclusion, map vs. image in L05's conclusion, function type vs. cardinality in L07's conclusion) are excellent pedagogical devices. The boss's addition of a cardinality conjunct is a genuine structural improvement from R1.

The single most important remaining issue is that **the world's cardinality teaching is entirely passive**. L07 is `exact Finset.card_image_le` (a one-liner). L08 Part B is `exact Finset.card_image_le` (the same one-liner). `card_image_of_injective` is declared in the inventory but never used. `card_map` is discussed in L05's introduction but never used. The learner reads about cardinality effects of image/map in four different places but never performs any cardinality reasoning. Fixing L07 (suggestion #1), ensuring `card_image_of_injective` is either used or removed from inventory (#3), and having L05 use `card_map` (#4) would transform cardinality from a read-only topic to an active one. These three changes together would address the world's most significant gap.
