# W16_ps BigOpPset -- Enrichment Review R1

## Ranked suggestions

### 1. Missing retrieval of `conv`, `gcongr`, and reindexing (V12, L12, L16)

**What**: The pset retrieves skills from W14 (induction), W15 (prod, algebraic manipulation), and the first half of W16 (filter, sum_comm), but completely omits the second half of W16: `conv` (L12), `gcongr` (L16), and reindexing via `sum_nbij'` / `sum_equiv` (V12). These are three major skills taught in W16 that get zero retrieval practice.

**Why**: A pset world that claims to cover "big-operator fluency" but skips three of the most technically demanding skills from the preceding lecture world leaves a large retrieval gap. `conv` is especially important because it is the gateway to all non-trivial manipulation inside binders, and it has no paper analogue -- making retrieval practice essential. `gcongr` and reindexing are the two hardest skills in W16 and are precisely the ones most likely to be forgotten without practice. The plan itself lists V12 and L12/L16 as coverage items in W16 but none appear in the pset's coverage column.

**Where**: New levels needed. Suggested insertions:
- A `conv`-based level (e.g., rewrite `∑ i ∈ range n, (i * (i + 1))` to `∑ i ∈ range n, (i^2 + i)` inside a binder, then decompose with `sum_add_distrib`). This would retrieve both L12 and V20 together.
- A `gcongr` level (e.g., given `∀ i ∈ range n, f i ≤ f i + 1`, prove `∑ f ≤ ∑ (f + 1)`). This retrieves L16.
- A reindexing level (e.g., prove `∑ i ∈ range n, f (i + 1) = ∑ j ∈ Ico 1 (n+1), f j` using `sum_nbij'`). This retrieves V12.

**Effort**: High (3 new levels).

**Recommend**: Yes. The omission of half of W16's content from the pset is a significant gap.

---

### 2. L03 claims `congr` retrieval but never uses `congr`

**What**: L03's plan entry says "Simplify a sum using `ring` and `congr`" and the coverage column lists "V20 (T), L7 (T)". But the actual proof is just `rw [Finset.sum_add_distrib]; rw [← Finset.mul_sum]` -- there is no `congr` (or `sum_congr` or `conv`) step at all. The `ring` tactic is also not used. The level retrieves V20 but does not retrieve L7 or any congr-family skill.

**Why**: The mismatch between the plan's coverage claim and the actual level means L7 (`ring`) has zero retrieval in this pset. Since `ring` is a core algebraic manipulation tactic introduced in W15, it needs at least one retrieval exercise. Additionally, if `congr` was planned, its absence means a congruence-inside-binders skill goes unpracticed.

**Where**: Modify L03. Add a step that requires `ring` or `congr` (e.g., the summand needs algebraic normalization before `sum_add_distrib` applies, requiring a `conv` + `ring` or `sum_congr` step first). Alternatively, keep L03 as-is but update its plan description to accurately reflect what it tests, and add the `ring` retrieval to a different level (e.g., the boss already uses `ring`, which partially covers this).

**Effort**: Medium (modify one level).

**Recommend**: Yes. Coverage claims should match reality, and `ring` deserves explicit retrieval.

---

### 3. L04 and L05 are one-tactic levels with no retrieval depth

**What**: L04 is `rw [Finset.sum_filter]` (one line). L05 is `exact Finset.sum_comm` (one line). These are the easiest possible exercises for their respective skills -- they are exact replays of what was taught, just with different constants.

**Why**: A pset world exists for retrieval under "reduced scaffolding" and "fresh surface forms." But applying a single lemma to a syntactically identical goal (just different numbers) is not retrieval -- it is repetition. The learner who completed W16 L01 (`sum_filter`) can mechanically replay L04 here without any cognitive effort. For a pset, these levels should combine the skill with another move, or require the learner to identify *when* to use the lemma rather than being told.

**Where**: Modify L04 and L05.
- L04: Instead of a direct `sum_filter` application, give a goal that requires the learner to first recognize that a conditional sum can be expressed as a filtered sum (i.e., the *reverse* direction), or combine filtering with another operation (e.g., filter then compute the result for small `n`).
- L05: Instead of a bare `sum_comm`, make the double sum require a preparatory step (e.g., rewrite the summand first, then interchange, then simplify). Or use `sum_comm` as a step in a multi-step proof.

**Effort**: Medium (modify two levels).

**Recommend**: Yes. One-tactic pset levels are pedagogically vacuous.

---

### 4. L06 transfer level has a trivially provable statement that teaches nothing in-game

**What**: L06 asks the learner to prove `X = X` by `rfl`, then presents the translation table in the conclusion. The entire pedagogical content is in passive reading (the conclusion text), not in active proving.

**Why**: Transfer levels are notoriously hard to make interactive in Lean, but a `rfl` proof is the absolute minimum. The learner skips past this level in seconds without engaging. A better design would require the learner to *construct* the equivalent expression. For example: "Here is `∑ i ∈ Finset.range n, (i ^ 2 + 1)`. Prove it equals `∑ i ∈ Finset.range n, (1 + i * i)`" -- forcing the learner to parse the sigma notation and recognize the algebraic equivalence. This is still a Lean exercise but it requires understanding the expression, not just typing `rfl`.

**Where**: Modify L06. Replace the `X = X` statement with something that forces engagement with the expression's structure while still being a lightweight level.

**Effort**: Medium (rewrite one level).

**Recommend**: Consider. Transfer levels are inherently limited in Lean, and the conclusion text is genuinely valuable. But even a trivial algebraic rearrangement would be better than `rfl`.

---

### 5. Boss level (L08) does not integrate filtering or reindexing

**What**: The boss is `∑ i ∈ range n, (2*i + 1) = n^2`, proved by pure induction + `ring`. It integrates V3 + V11 + V20 -- the same skills as L01 but slightly harder. It does not integrate any W16-specific content: no filtering (M38), no `sum_comm` (M26), no reindexing (V12), no `conv` (L12), no `gcongr` (L16).

**Why**: A pset boss should integrate skills from the entire block being reviewed, not just the easiest subset. The current boss is essentially a harder version of L01 and could have appeared as L02 or L03. A true integration boss might require the learner to decompose a sum by filtering, reindex one piece, and close with induction. That would genuinely test whether the learner can orchestrate multiple big-operator skills.

**Where**: Replace L08 with a more integrative boss, or add a second boss that exercises W16-specific skills. Example: prove `∑ i ∈ range (2*n), (-1)^i = 0` by splitting into even and odd terms (filter), rewriting each piece, and showing cancellation. Or prove an identity about `∑ i ∈ range n, f i = ∑ i ∈ range n, f (n - 1 - i)` using reindexing.

**Effort**: High (redesign or add one level).

**Recommend**: Yes. The boss must integrate across the full skill set, not just the induction subset.

---

### 6. No level exercises the multiplicative-to-additive transfer pattern

**What**: L01 is additive induction (sum of 2s), L02 is multiplicative induction (product of 3s). But no level asks the learner to recognize the structural parallel between them or to apply a technique learned in one setting to the other.

**Why**: The additive/multiplicative duality is a key proof-move insight from W15. A pset level that explicitly asks "do the same thing you just did for sums, but for products" is a low-effort opportunity that's already implicitly present (L01 and L02 are parallel) but never articulated. Adding a sentence to L02's introduction like "Notice how this proof is structurally identical to L01, with `sum` replaced by `prod`, `0` replaced by `1`, and `+` replaced by `*`" would cost almost nothing and reinforce a transferable insight.

**Where**: Modify L02 introduction or conclusion.

**Effort**: Low (add a sentence).

**Recommend**: Yes. The parallel is already there; just name it.

---

### 7. The world introduction (L01) references "W13-W16" but these are internal world numbers, not world names

**What**: L01's introduction says "retrieve skills from the big-operator worlds (W13-W16)." The learner sees world *names* (like "RangeSumInduction", "FinsetProd", "BigOpAdvanced"), not internal numbering like "W13."

**Why**: This breaks the fourth wall. The learner has no way to map "W13" to a world they played. Use the world names or describe the content directly ("the induction, product, and advanced big-operator worlds").

**Where**: Modify L01 introduction.

**Effort**: Low (edit one sentence).

**Recommend**: Yes. Trivial fix, clear improvement.

---

### 8. L07 transfer proof duplicates L01's identity (sum of constants)

**What**: L07 asks the learner to prove `∑ i ∈ range n, 5 = 5 * n`. L01 already proved `∑ i ∈ range n, 2 = 2 * n`. These are the same identity with a different constant. The learner proves structurally identical inductive proofs twice in the same world.

**Why**: The transfer level's pedagogical value is in the conclusion (the paper proof translation), not the Lean proof itself. But the duplication means the learner experiences deja vu rather than fresh challenge. If the Lean proof is going to be trivial anyway, use a different identity for the transfer -- perhaps one involving a non-constant summand (like the sum of `i` or the sum of `2*i + 1` from L08), so the paper proof translation shows a more interesting inductive step.

**Where**: Modify L07 to use a more interesting identity for the paper translation. The sum of first `n` natural numbers (`∑ i = n(n-1)/2`) or the geometric sum would provide a richer paper proof to translate.

**Effort**: Medium (rewrite one level).

**Recommend**: Consider. The duplication is real but the transfer content in the conclusion is independent of which identity is used. Still, variety is free.

---

### 9. No "what if?" or misconception level

**What**: The pset has no level that challenges a false generalization or explores what happens when a hypothesis is missing.

**Why**: Pset worlds are an ideal venue for misconception levels because the learner is past the initial learning phase and ready for adversarial challenges. Examples: "Can you interchange summation order when the index sets are different?" (yes, `sum_comm` still works -- this corrects a possible misconception that it only works for identical ranges). Or: "Does `sum_filter` work for products?" (yes, via `prod_filter`). These are low-cost, high-insight levels.

**Where**: New level(s), or modify existing levels to include a misconception moment.

**Effort**: Medium (1 new level or modifications to existing levels).

**Recommend**: Consider. Not every pset needs misconception levels, but the complete absence is notable.

---

### 10. The conclusion of L08 mentions "geometric interpretation" but it is text-only

**What**: The boss conclusion describes the geometric interpretation of `1 + 3 + 5 + ... + (2n-1) = n^2` (L-shaped borders on a square) but only in text. There is no level that exercises this geometric intuition.

**Why**: The geometric proof is one of the most famous visual arguments in mathematics. While a Lean game cannot directly test visual reasoning, it could ask the learner to prove the algebraic step that corresponds to the geometric insight: `n^2 + (2*n + 1) = (n + 1)^2`. This is already implicit in the inductive step of L08, but isolating it as a standalone lemma before the boss would make the geometric connection concrete rather than decorative.

**Where**: Could be a `have` step within L08 that is explicitly named, or a brief level before the boss.

**Effort**: Low-Medium (add a `have` step or a short pre-boss level).

**Recommend**: Consider. The geometric insight is valuable but may be better served by the text alone.

---

## Overall impression

BigOpPset is structurally sound as a retrieval world: it moves through additive induction, multiplicative induction, algebraic manipulation, filtering, double sums, transfer, and a boss in a clean linear progression. The transfer levels (L06, L07) are a genuine strength -- the Lean-to-paper correspondence tables are clear and well-constructed, and the boss conclusion's geometric interpretation is a nice touch.

**The single most important improvement is suggestion #1**: the world completely omits retrieval of `conv`, `gcongr`, and reindexing -- three of the hardest and most important skills from the preceding W16 lecture. These are precisely the skills that need pset practice most, because they are complex enough to be forgotten and procedurally demanding enough that repetition builds fluency. Adding even two levels (one for `conv` + algebraic manipulation, one for reindexing or `gcongr`) would transform this pset from a partial review of the easy skills into a genuine fluency workout across the full big-operator toolkit. The boss should also be redesigned to integrate across the full skill set rather than being an induction-only exercise.
