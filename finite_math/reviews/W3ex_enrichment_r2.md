# Enrichment Review: W3_ex (FinThreeExamples) -- Round 2

## Ranked Suggestions

### 1. The involution property of the swap is an obvious derivable result that goes unstated

**What**: L10 introduces the swap permutation `0 -> 0, 1 -> 2, 2 -> 1` and proves it is bijective, but never observes that it is an **involution** -- applying it twice gives the identity. This is a derivable result from the data already in the level, and it is the most natural mathematical observation about a swap.

**Why**: The involution property (`f (f i) = i` for all `i : Fin 3`) is the single most important structural fact about a transposition. It connects to order of a permutation, to the distinction between the cyclic shift (order 3) and the swap (order 2), and to the concept of inverse functions. A learner who proves bijectivity of both the cyclic shift and the swap without noticing their orders has missed the deepest lesson that the two examples together can teach. The proof is `intro i; fin_cases i <;> rfl` -- essentially free -- so the cost is a few lines of introduction and conclusion text plus a new Statement.

**Where**: New level, inserted between L09 (bijectivity) and L10 (boss). The current L10 becomes L11. Alternatively, the involution property could be integrated into the boss itself as a second conjunct.

**Effort**: Medium (add a new level or extend the boss statement).

**Recommend**: Yes.

---

### 2. The cyclic shift and the swap are two of the six permutations of Fin 3 -- name them

**What**: The conclusion of L09 mentions "6 permutations of `Fin 3`" and the boss conclusion mentions `Equiv.Perm (Fin 3)`, but the world never asks the learner to think about what the other four permutations are. A brief enumeration in a conclusion -- or better, a "What if?" moment -- would ground the counting claim.

**Why**: The world proves bijectivity for exactly two of the six permutations. Listing all six (identity, two 3-cycles, three transpositions) in a conclusion gives the learner a complete picture and connects to the factorial counting principle (3! = 6) introduced by name in L09's conclusion. Without the enumeration, "6 permutations" is an assertion the learner must take on faith.

**Where**: L09 conclusion or L10 conclusion. A table listing the six permutations (by their lookup tables) with labels like "identity", "cyclic shift", "reverse cyclic shift", "swap 0-1", "swap 0-2", "swap 1-2" would cost about 10 lines.

**Effort**: Low (add to an existing conclusion).

**Recommend**: Yes.

---

### 3. L09 re-proves injectivity and surjectivity from scratch instead of combining prior results

**What**: L09 asks the learner to prove bijectivity of the cyclic shift by re-doing the full injectivity and surjectivity proofs from L04 and L05. The integration skill being tested is `constructor`, not the exhaustive proofs themselves. But since the function is the same, the learner is literally repeating work rather than *combining* work.

**Why**: The pedagogical claim in the introduction -- "This level is about **integration**: combining two previously practiced proof moves" -- is accurate in spirit but misleading in practice. True integration would involve citing or referencing previously established results. The level as written tests "can you type the same proof twice in one file", not "can you combine two subresults." This is an inherent limitation of the lean4game framework (levels do not share named theorems), so the solution is not to change the proof, but to **acknowledge the repetition explicitly** in the introduction: "In a real Lean development, you would name the injectivity and surjectivity lemmas and combine them. In this game, we practice the combination by proving both parts inside a single structured proof." This reframes the repetition as a deliberate pedagogical choice rather than an oversight.

**Where**: L09 introduction.

**Effort**: Low (add 2-3 sentences to the introduction).

**Recommend**: Yes.

---

### 4. No level asks "how many injections/surjections are there?" -- a missed counting connection

**What**: The world proves that one specific function is injective (L04) and another is not (L07), but never asks the learner to think about *how many* injections `Fin 3 -> Fin 3` exist, or how many surjections. The answer (6 for both, since on same-size sets injectivity = surjectivity = bijectivity, and there are 3! = 6 bijections) connects the function-analysis work to the counting work in L08 and previews the later counting worlds.

**Why**: The world already has both the function analysis (L04-L07, L09-L10) and the cardinality tools (L08), but these two threads never meet. A question in a conclusion like "You proved one specific injection. How many injections `Fin 3 -> Fin 3` exist? Since injectivity on a set of size 3 is the same as bijectivity, the answer is 3! = 6 -- the number of permutations" would tie the threads together and preview W12 (counting) and W22 (permutations).

**Where**: L04 conclusion, L09 conclusion, or L10 conclusion.

**Effort**: Low (add to an existing conclusion).

**Recommend**: Consider.

---

### 5. L03 misses the opportunity to connect pair counting to L08's cardinality result

**What**: L03 constructs a single pair `(0, 1)` in `Fin 3 x Fin 3` with distinct components. L08 proves `Fintype.card (Fin 3 x Fin 3) = 9`. The conclusion of L03 states "of these, 6 have distinct components (the off-diagonal entries)" -- a counting claim that is never proved. A forward reference in L03's conclusion to L08, or a brief derivation of "6 off-diagonal pairs" in L08's conclusion, would close this gap.

**Why**: The claim "6 off-diagonal" is a concrete example of inclusion-exclusion (9 total minus 3 diagonal = 6 off-diagonal). This is a preview of W9 (cardinality) and could be signposted.

**Where**: L08 conclusion, adding: "Of the 9 pairs, 3 lie on the diagonal (both components equal). So 9 - 3 = 6 pairs have distinct components -- confirming the count mentioned in Level 3."

**Effort**: Low (add 1-2 sentences to L08 conclusion).

**Recommend**: Consider.

---

### 6. The "congr_arg Fin.val" pattern is used repeatedly but never named as a strategy

**What**: The pattern `have := congr_arg Fin.val h; norm_num at this` appears in L03, L04, L07, L09, and L10. It is used to extract a value-level equation from a `Fin`-level equation and derive a numeric contradiction. Despite being the most-used proof pattern in the world, it is never given a name or identified as a reusable strategy.

**Why**: Naming a strategy makes it transferable. The learner who recognizes "extract-value-and-contradict" as a named move will be able to apply it on `Fin 5`, `Fin 100`, or any other `Fin n` without re-deriving the pattern. The conclusion of L03 partially does this ("The pattern... is worth remembering"), but later levels do not use the same language. Using a consistent name -- e.g., "the **Fin.val extraction** move" or "the **value contradiction** pattern" -- across conclusions would reinforce retention.

**Where**: L03 conclusion (where the pattern is first used), then refer back to it by name in L04, L07 conclusions.

**Effort**: Low (edit 3-4 conclusion paragraphs to use consistent terminology).

**Recommend**: Yes.

---

### 7. L06 and L07 are duals but the duality is only mentioned in L07 -- not in L06

**What**: L06 proves `Fin 3 -> Fin 4` is not surjective; L07 proves `Fin 4 -> Fin 3` is not injective. The conclusion of L07 explicitly connects these as "two faces of the same coin -- the pigeonhole principle." But L06's conclusion does not foreshadow L07 or mention the duality. A sentence at the end of L06's conclusion like "In the next level, you will see the dual failure: too many inputs for too few outputs" would prepare the learner for the connection.

**Why**: The duality is one of the deepest insights in this world. Surfacing it from both sides (not just in L07 looking back) ensures the learner who pauses between levels still gets the foreshadowing.

**Where**: L06 conclusion, last paragraph.

**Effort**: Low (add 1-2 sentences).

**Recommend**: Consider.

---

### 8. L08 proves cardinality of `Fin 3 x Fin 3` but never asks about `Fin 3 + Fin 3` (sum type)

**What**: L08 teaches the multiplication principle via `Fintype.card_prod`. The additive counterpart -- `Fintype.card (Fin 3 + Fin 3) = 6` via `Fintype.card_sum` -- is a natural companion that goes unmentioned. It would preview W12's treatment of sum types.

**Why**: The multiplication principle is only half of the most basic counting principles. The addition principle (disjoint union has cardinality equal to the sum of cardinalities) is the other half. Mentioning it in L08's conclusion -- even without a proof -- would complete the conceptual pair.

**Where**: L08 conclusion, adding: "There is also an **addition principle**: `Fintype.card (Fin 3 + Fin 3) = 3 + 3 = 6`. You will prove this in a later world."

**Effort**: Low (add 1-2 sentences to conclusion).

**Recommend**: Consider.

---

### 9. The boss (L10) uses a conjunction `Injective f /\ Surjective f` instead of `Bijective f`

**What**: L10's statement is `Function.Injective f /\ Function.Surjective f` rather than `Function.Bijective f`, even though L09 already introduced `Function.Bijective` and showed it equals `Injective /\ Surjective`. This means the boss does not require the learner to recall that `Bijective = Injective /\ Surjective`.

**Why**: Using `Bijective f` as the boss statement would require one additional `unfold` or `show` step, testing whether the learner remembers the equivalence from L09. The current formulation skips this recall opportunity. However, this is a minor point -- the boss is already testing integration, and adding an extra `unfold` layer risks obscuring the main point with a syntactic detour.

**Where**: L10 statement.

**Effort**: Low (change the statement type, add one `unfold` hint).

**Recommend**: Consider.

---

### 10. No level explores what happens when you compose two permutations of Fin 3

**What**: The world studies two permutations of `Fin 3` (the cyclic shift and the swap) in isolation but never composes them. Composition is the fundamental operation on permutations. A level proving `swap (shift i) = ...` or computing the composition table would deepen the example significantly and preview W22 (permutations).

**Why**: Composition is what turns the set of permutations into a group. The world has all the ingredients (two named permutations, `fin_cases` as the proof tool) but stops short of the most natural operation. However, this would require a new level and potentially expand the world beyond its "example world" scope.

**Where**: New level between L09 and L10 (or replacing L10 with a richer boss).

**Effort**: High (new level with nontrivial statement and proof).

**Recommend**: Consider.

---

## Overall Impression

The rewritten world is a substantial improvement over round 1. The 10-level structure has a clear narrative arc (enumerate -> compute -> construct -> inject -> surject -> fail to surject -> fail to inject -> count -> biject -> boss), every level has `DisabledTactic` preventing trivial automation, every level has contextual hints at multiple granularity levels, and the introductions and conclusions do genuine pedagogical work -- explaining proof shapes, providing transfer moments, and connecting to the broader course. The consistent use of the same cyclic shift function across L04, L05, and L09 is a strong design choice that lets the learner see the same object through multiple theoretical lenses.

The single most important improvement is **Suggestion 1**: adding the involution property of the swap (or naming the order difference between the cyclic shift and the swap). The world currently treats both permutations as "things to prove bijective" without observing their most distinguishing structural property. Adding this observation -- even as a 2-line level -- would elevate the world from "a collection of function-property exercises" to "a study of two genuinely different permutations," which is the deeper mathematical lesson the examples can teach.
