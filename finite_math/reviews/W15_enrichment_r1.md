# W15 FinsetProd -- Enrichment Review (Round 1)

## Ranked suggestions

### 1. The boss does not use `Finset.prod` at all -- the world's namesake is absent from integration

**What**: The boss level (L08) is entirely about sum manipulation (`sum_congr`, `sum_add_distrib`, `mul_sum`). Despite the world being titled "Finset.prod and algebraic manipulation," the product operator is never required after L04. The boss should integrate both sum and product manipulation.

**Why**: The world promise says the learner "understands `Finset.prod`, can work with both additive and multiplicative big operators, and can do algebraic manipulation inside big-operator goals." But the boss only tests sum manipulation. A learner could complete L08 having forgotten everything about products. The plan row for L08 explicitly says "Prove an identity that requires both `sum` and `prod` manipulations," but the implementation only uses sums.

**Where**: L08 (Boss). Replace or extend the boss statement to require at least one `prod`-side manipulation (e.g., `prod_congr`, `prod_mul_distrib`, or `prod_range_succ`) alongside the sum manipulations.

**Effort**: High (rewrite the boss level statement and proof).

**Recommend**: Yes.

---

### 2. `prod_mul_distrib` is mentioned in L05's conclusion but never exercised

**What**: L05 introduces `sum_add_distrib` and documents `prod_mul_distrib` in the conclusion and `TheoremDoc`. But no level asks the learner to use `prod_mul_distrib`. It is introduced as inventory but never practiced.

**Why**: The sum/product duality is a central theme of this world. Every sum lemma (`sum_add_distrib`, `mul_sum`, `sum_congr`) gets its own exercise, but the product counterparts (`prod_mul_distrib`, `prod_congr`) are only mentioned in conclusions. This is a missed opportunity to reinforce the duality pattern. A learner who has only ever applied the sum version will not confidently reach for the product version in later worlds.

**Where**: Add a level (or extend L05) that asks the learner to apply `prod_mul_distrib` to a concrete product, mirroring the L05 exercise. Alternatively, fold a `prod_mul_distrib` step into the redesigned boss.

**Effort**: Medium (add a level or modify the boss).

**Recommend**: Yes.

---

### 3. `ring` is introduced (L04) with no isolation of the tactic itself -- it is tangled with induction and `prod_range_succ`

**What**: L04 is supposed to introduce `ring` (plan: "Introducing ring: Use ring to close algebraic subgoals inside big-operator proofs," coverage item L7 (I)). But the level is a full induction proof (`∏ i in range n, 2 = 2^n`) that requires `induction`, `rfl`, `prod_range_succ`, `ih`, and `ring`. The dominant lesson is induction on products, not `ring`.

**Why**: The first time a learner encounters `ring`, the level should isolate it so the learner can focus on what `ring` does and when to use it. Combining it with a three-step induction proof means a stuck learner cannot tell whether their confusion is about `ring` or about the induction structure. The quality standards say "A level should usually have one dominant lesson" and "first contact: heavy explanation, explicit docs, rescue hints." L04 does not give `ring` first-contact treatment.

**Where**: Insert a new level before current L04 that introduces `ring` in isolation. For example: prove `2 * 3 + 5 = 11` or `a * (b + c) = a * b + a * c` using just `ring`. Then the current L04 becomes the second contact where `ring` appears inside a larger proof.

**Effort**: Medium (add one new level, renumber subsequent levels).

**Recommend**: Yes.

---

### 4. No `NewTactic` declaration for `ring` -- the tactic is introduced but not registered in inventory

**What**: L04 introduces `ring` as a new tactic (plan says L7 (I)) but the file has no `NewTactic ring` or `TacticDoc ring` declaration.

**Why**: Without `NewTactic`, the lean4game UI will not show `ring` in the learner's inventory panel. The learner will see it in hints but it will not appear as a newly unlocked tool. This is both a pedagogical gap (the UI should celebrate new tools) and a potential build warning (missing TacticDoc).

**Where**: L04 (or the new isolated `ring` level if suggestion 3 is adopted).

**Effort**: Low (add two declarations).

**Recommend**: Yes.

---

### 5. The sum/product duality is never explicitly named as a transferable pattern

**What**: The world shows parallel lemmas (`sum_empty`/`prod_empty`, `sum_singleton`/`prod_singleton`, `sum_range_succ`/`prod_range_succ`, `sum_add_distrib`/`prod_mul_distrib`, `sum_congr`/`prod_congr`) but never names this duality as a systematic pattern. The L01 conclusion has a table, but no level or conclusion says "in mathlib, every `sum_X` lemma has a `prod_X` counterpart, and you can predict one from the other."

**Why**: Naming the pattern is a transfer opportunity. When the learner later encounters an unfamiliar product lemma, they should think "I know the sum version; the product version must exist and look like this." The table in L01 is close but only compares notation, not the API mirroring principle. A single sentence in L05's or L07's conclusion that explicitly states the duality principle would cost nothing and give the learner a prediction tool.

**Where**: L05 conclusion or L07 conclusion (wherever the duality is most salient).

**Effort**: Low (one paragraph in a conclusion).

**Recommend**: Yes.

---

### 6. L01 introduces `prod_singleton` but L02 re-teaches `prod_singleton` conceptually (title says "prod_empty and prod_singleton") -- the singleton case is redundant

**What**: L01's statement is `∏ x in {3}, x = 3`, which is solved by `prod_singleton`. L02's title is "prod_empty and prod_singleton" and its introduction mentions both, but the actual statement only exercises `prod_empty`. Despite this, the world recaps `prod_singleton` in L02's conclusion table. The title is misleading.

**Why**: A learner who just proved `prod_singleton` in L01 will expect L02 to teach something new about singletons, but the level only does `prod_empty`. The title should match the content. This is not a major pedagogical issue, but the mismatch between title and content is confusing.

**Where**: L02. Rename to "The empty product" or make the level a two-part exercise that genuinely uses both.

**Effort**: Low (rename the level title).

**Recommend**: Consider.

---

### 7. No concrete computation level showing what a product evaluates to numerically

**What**: L01 computes `∏ x in {3}, x = 3` (trivial singleton) and L03 peels off a factor but leaves the product unevaluated. No level asks the learner to fully evaluate a product like `∏ i in range 4, (i + 1) = 24` (i.e., 4! = 24). L04 does `∏ i in range n, 2 = 2^n` but that is a symbolic identity, not a numeric computation.

**Why**: Concrete computation builds intuition. The sum world (W13) likely had levels where the learner evaluated a sum to a specific number. The product world should have the same. Computing `1 * 2 * 3 * 4 = 24` and recognizing it as 4! creates a mental model that will be essential in W17 (Factorials). This also previews the factorial connection (plan: M27, W17).

**Where**: After L03 (or as part of L03). Add a level where the learner fully evaluates `∏ i in range 4, (i + 1)` to `24` by repeated application of `prod_range_succ` and `prod_empty` or `prod_singleton`, followed by `ring` or `norm_num`.

**Effort**: Medium (add one level).

**Recommend**: Yes.

---

### 8. L05 and L06 are one-step levels -- the proofs are single `rw` calls with no multi-step reasoning

**What**: L05 (sum_add_distrib) and L06 (mul_sum) each have a Statement that is closed by a single `rw` call. The learner types one tactic and the level is done.

**Why**: Single-tactic levels are appropriate for first introduction (I-stage), and these levels are correctly at the I-stage. However, the lack of any follow-up work means the learner has no chance to internalize the rewrite direction or deal with the "which direction do I rewrite?" question. L06's introduction discusses left-vs-right direction (`mul_sum` vs `← mul_sum`) but the exercise only requires one direction. A second part (or a companion level) that requires the reverse direction would make the lesson stick.

**Where**: L05 and/or L06. Either make the level a two-part exercise (prove one direction, then the other) or add a follow-up level that requires the reverse rewrite.

**Effort**: Medium (modify or add levels).

**Recommend**: Consider.

---

### 9. No foreshadowing of W16 concepts (`conv`, `sum_comm`, `sum_filter`) in the conclusion

**What**: The L08 conclusion says "The next world introduces splitting, filtering, and reindexing" but does not mention any specific concepts or why they matter. W16 introduces `conv` (L12), `gcongr` (L16), and `sum_comm` (M26) -- all major new tools. A brief sentence about what problem these tools solve would prime the learner.

**Where**: L08 conclusion.

**Effort**: Low (add 2-3 sentences).

**Recommend**: Consider.

---

### 10. `sum_congr` (L07) presents two alternative proof paths but does not explain when to prefer each

**What**: L07 teaches `apply Finset.sum_congr rfl` and also mentions `congr 1` + `ext` as an alternative. Both are shown but there is no guidance on when to prefer one over the other.

**Why**: A learner who sees two ways to do the same thing will wonder "which should I use?" The answer matters: `sum_congr rfl` is more explicit and works when you need fine control over the membership proof; `congr 1; ext` is more concise and works well when the pointwise equality is straightforward. Stating this distinction builds proof strategy knowledge (the MOVE layer).

**Where**: L07 conclusion.

**Effort**: Low (add a short paragraph).

**Recommend**: Consider.

---

### 11. `prod_congr` is documented (L07) but never exercised

**What**: L07 introduces `Finset.prod_congr` in the TheoremDoc and mentions it in the conclusion, but the exercise only uses `sum_congr`. This is similar to suggestion 2 (prod_mul_distrib never exercised).

**Why**: Same duality concern. The product version should appear at least once as an exercise, ideally in the boss or as a short level after L07.

**Where**: New level after L07 or in the redesigned boss.

**Effort**: Medium (add a level or fold into boss).

**Recommend**: Yes (if addressing suggestion 1, fold this into the redesigned boss).

---

## Overall impression

The world has a clean pedagogical arc: introduce the product operator (L01-L03), show how `ring` closes algebraic subgoals (L04), teach three algebraic manipulation lemmas for sums (L05-L07), and integrate in a boss (L08). The introductions and conclusions are well-written, with good mathematical context and clear lemma statements. The sum/product comparison tables in L01 and L02 are effective. The level-by-level progression is logical and the hint scaffolding is appropriate.

**The single most important improvement** is redesigning the boss (L08) to actually require product manipulation alongside sum manipulation. As currently written, the world teaches `Finset.prod` in L01-L04 and then pivots entirely to sum manipulation in L05-L08, making the product material feel disconnected. The world promises integration of both, and the plan explicitly calls for "both sum and prod manipulations" in the boss, but the implementation delivers only sums. A boss that requires, say, `prod_congr` or `prod_mul_distrib` alongside `sum_add_distrib` and `mul_sum` would unify the world's two halves and make the "Finset.prod and algebraic manipulation" title honest. Suggestions 2 and 11 (exercising `prod_mul_distrib` and `prod_congr`) could be addressed simultaneously by folding product-side steps into a redesigned boss.
