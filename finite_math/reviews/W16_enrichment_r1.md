# W16 BigOpAdvanced — Enrichment Review (Round 1)

**Reviewer**: enrichment-reviewer
**Date**: 2025-03-15
**World**: W16 BigOpAdvanced (9 levels)
**World type**: Lecture
**World promise**: The learner can split sums by predicate, filter sums, and reindex using `sum_bij` or `sum_equiv`.

---

## Ranked suggestions

### 1. The plan calls L02 "sum_ite" but the level is actually "sum_filter_add_sum_filter_not" — the `Finset.sum_ite` lemma itself is never taught

**What**: The plan's L02 says the dominant lesson is "`sum_ite`: Split a sum by a conditional" (coverage item M38 (S)), but the actual L02 teaches `sum_filter_add_sum_filter_not`, which is a different lemma. The real `Finset.sum_ite` (which converts `∑ i in s, if p i then f i else g i` into `(∑ i in s.filter p, f i) + (∑ i in s.filter (not p), g i)`) is never introduced. This matters because `sum_ite` is the *reverse* direction of `sum_filter` and is the more commonly needed tool in practice — you encounter conditional expressions inside sums and want to split them. The current L01 goes from filter to conditional; the missing `sum_ite` goes from conditional to filter. These are complementary, and the learner needs both.

**Why**: `sum_ite` is explicitly listed as a plan coverage item (M38). More importantly, the learner who encounters `∑ i in s, if p i then f i else g i` in later worlds (W16_ps L04, W19) will need to decompose it. Without seeing `sum_ite`, they only know one direction of the filter/conditional correspondence.

**Where**: Add a new level between current L02 and L03 (making it L03, shifting subsequent levels). The new level should present a goal like `∑ i in range n, if Even i then i^2 else i = (∑ i in (range n).filter Even, i^2) + (∑ i in (range n).filter (not Even), i)` and have the learner apply `Finset.sum_ite`.

**Effort**: High (new level)
**Recommend**: Yes

---

### 2. L02 is a single `exact` call — too shallow for the "filter decomposition" lesson

**What**: L02 asks the learner to prove `(∑ i in (range n).filter Even, i) + (∑ i in (range n).filter (not Even), i) = ∑ i in range n, i` and the entire proof is `exact Finset.sum_filter_add_sum_filter_not _ Even _`. This is a one-tactic "apply the API" level with zero proof moves. The conclusion talks about "the splitting principle" being "one of the most useful identities in combinatorics," but the learner does not actually *use* it — they just cite it.

**Why**: Filter decomposition is a proof *strategy* (split by predicate, simplify each piece separately). The learner should experience the strategy, not just name-drop the lemma. A level that asks the learner to *use* the decomposition to compute something would be far more instructive. For example: prove that `∑ i in range (2*n), i = 2 * ∑ i in range n, (2*i) + n` by first splitting into even and odd parts, then simplifying each piece.

**Where**: Replace or significantly restructure L02 so the learner applies `sum_filter_add_sum_filter_not` as a *step* in a multi-step proof, not as the whole proof.

**Effort**: Medium (rewrite one level)
**Recommend**: Yes

---

### 3. L04 (`sum_comm`) is also a single `exact` call — the learner never experiences *why* you interchange summation

**What**: L04 proves `∑ i in range 3, ∑ j in range 4, f i j = ∑ j in range 4, ∑ i in range 3, f i j` with `exact Finset.sum_comm`. The conclusion mentions that "interchanging the summation order is often the key first step in a much harder proof," but the learner never takes that step. They just apply the commutativity lemma.

**Why**: `sum_comm` is not interesting as a standalone identity — it is interesting because it enables simplifications. The pedagogical value is in the "swap and simplify" pattern. A better goal would require swapping the order *because* one order makes an inner sum collapse. For example, `∑ i in range n, ∑ j in range n, min i j` can be simplified after rewriting, or more simply, a double sum where one summation order makes `sum_const` applicable.

**Where**: Replace L04 with a problem where `sum_comm` is a key step but not the entire proof. The learner should need to apply `sum_comm` and then simplify the result.

**Effort**: Medium (rewrite one level)
**Recommend**: Yes

---

### 4. L01 (`sum_filter`) is also a single `rw` call — the first three levels are all one-tactic proofs

**What**: L01, L02, and L04 are each solved with a single tactic (`rw`, `exact`, `exact`). Three of the first four levels being one-step proofs makes the opening of this world feel like an API tour rather than a world that teaches proof moves. L03 is also a single `exact` call.

**Why**: A LECTURE world should teach *how to use* these tools, not merely introduce their names. The one-step levels are appropriate as the *first* encounter with a lemma (which L01 is), but when they cluster, the learner is not building any proof construction skill. At minimum, L01 should be the only one-tactic level in the opening block.

**Where**: This is addressed by suggestions 2 and 3 above. If those are implemented, this problem is solved.

**Effort**: Low (covered by other suggestions)
**Recommend**: Yes (but implementation is via suggestions 2 and 3)

---

### 5. The boss level (L09) does not use filtering, splitting by predicate, or reindexing — it only uses `conv`, `sum_add_distrib`, `sum_const`, and `mul_sum`

**What**: The plan says L09 should be "a splitting + reindexing proof" that integrates "M25, M26, M38, V12." But the actual boss level is a double-sum decomposition `∑ i, ∑ j, (i+j) = m*(∑ i) + n*(∑ j)` that uses `conv`, `sum_add_distrib`, `congr`, `sum_const`, `card_range`, and `mul_sum`. It never uses `sum_filter`, `sum_filter_add_sum_filter_not`, `sum_comm`, `sum_nbij'`, or `sum_equiv`. It does not use filtering (M38), does not interchange summation (M26), and does not reindex (V12). It essentially tests only the W15 skills (`sum_add_distrib`, `sum_const`, `mul_sum`) plus the new `conv` tactic.

**Why**: The boss should be a capstone that integrates the world's dominant lessons. A boss that does not use the world's main topics (filtering, reindexing) is misleading. The learner completes the world thinking they have mastered the material, but the boss did not exercise the hard skills.

**Where**: Replace L09 with a problem that requires at least two of: predicate-based splitting, summation interchange, and reindexing. For example, prove an identity like `∑ i in range n, ∑ j in range n, (if i ≤ j then f i j else 0) = ∑ j in range n, ∑ i in range (j+1), f i j`, which requires `sum_comm` + `sum_filter` + possibly reindexing. Or prove a Gauss-style identity that uses reindexing to pair terms: `2 * ∑ i in range n, i = n * (n-1)` by reindexing and adding the original sum to its reverse.

**Effort**: High (rewrite boss level)
**Recommend**: Yes

---

### 6. `sum_nbij'` is introduced but `Finset.sum_bij` is never shown, despite being named in the world promise

**What**: The world promise says "reindex using `sum_bij` or `sum_equiv`." The levels teach `sum_nbij'` (L07, L08) and mention `sum_equiv` (L08 conclusion), but `sum_bij` is never introduced. `sum_bij` is the classical one-sided bijection interface (forward map + injectivity + surjectivity + function-value match), which is sometimes more natural than `sum_nbij'` (where you must provide both maps).

**Why**: In some reindexing situations, stating the inverse explicitly is unnatural (e.g., when the bijection is not a simple arithmetic shift). `sum_bij` lets you prove injectivity and surjectivity instead of providing an explicit inverse. Showing both tools gives the learner a choice and deepens understanding of what "bijective reindexing" really requires.

**Where**: Mention `sum_bij` in the L07 or L08 conclusion as an alternative. Ideally, add a brief worked example showing when `sum_bij` is more convenient (a remark, not necessarily a full level).

**Effort**: Low (add a paragraph to L07 or L08 conclusion)
**Recommend**: Consider

---

### 7. No level motivates *why* reindexing is useful — the reindexing examples are tautological

**What**: L07 proves `∑ i in range 4, (i+5) = ∑ j in Ico 5 9, j` and L08 proves `∑ i in range n, (i+1) = ∑ j in Ico 1 (n+1), j`. Both of these are "the same sum written two ways" — the learner proves they are equal, but never sees a situation where reindexing *enables* a simplification. The result of the reindexing is no simpler than the starting expression.

**Why**: Reindexing is powerful because it lets you *align* two sums so that terms cancel or match. The learner should see a problem where reindexing is the key insight, not just the technique. For example: proving that `∑ i in range n, f i = ∑ i in range n, f (n - 1 - i)` (reversing a sum) is the canonical motivating example because it enables the Gauss pairing trick.

**Where**: The plan's L07 actually says "Reindex `sum i in range n, f i` to `sum i in range n, f (n - 1 - i)`" — which is exactly the reversal example. But the actual L07 does a simple shift instead. Consider making L07 or L08 the reversal example, which is both more interesting and more representative of how reindexing is used in practice.

**Effort**: Medium (rewrite L07 or L08)
**Recommend**: Yes

---

### 8. `conv_lhs` and `conv_rhs` are taught but `conv in ...` pattern is not mentioned

**What**: L05 teaches the `conv_lhs => arg 2; ext i; rw [...]` pattern. This works but is positional (`arg 2`), which is fragile and hard to read. The `conv in (pattern) => rw [...]` form is more readable and robust for many use cases. It targets by pattern matching rather than position.

**Why**: When learners encounter `conv` in later worlds or their own proofs, the positional navigation (`arg 1`, `arg 2`) will be confusing if the term structure is not obvious. Mentioning `conv in` as an alternative (even in the conclusion) gives them a fallback they can use when positional navigation is unclear.

**Where**: Add a note in L05's conclusion mentioning `conv in` as an alternative pattern.

**Effort**: Low (sentence in conclusion)
**Recommend**: Consider

---

### 9. No level teaches `Finset.sum_ite_eq'` or `Finset.sum_ite_eq` — the "Kronecker delta" pattern

**What**: The filter/conditional block (L01-L02) introduces `sum_filter` and `sum_filter_add_sum_filter_not`, but misses the important special case: when the predicate is `(· = a)`, the filtered sum extracts a single term. This is `Finset.sum_ite_eq'`: `∑ i in s, if i = a then f i else 0 = if a ∈ s then f a else 0`. This is the Kronecker delta in disguise and is used constantly in linear algebra (matrix entries, basis decompositions).

**Why**: This is a natural example of filtering that connects to W23 (matrices) and is an excellent instance of the "filter extracts a single element" pattern. It would make filtering feel less abstract and more practically useful.

**Where**: Add as a level after the current L02 (in the filter block), or mention it in L01's conclusion as a notable special case.

**Effort**: Medium (new level) or low (conclusion note)
**Recommend**: Consider

---

### 10. The world introduction (L01) mentions "three powerful new skills" but the list does not include `gcongr`

**What**: L01's introduction says "This world teaches you three powerful new skills: 1. Filtering and splitting, 2. `conv` and `gcongr`, 3. Reindexing." This bundles `conv` and `gcongr` together. But `gcongr` is a fundamentally different tool (inequality reasoning) from `conv` (targeted rewriting). Bundling them undersells `gcongr`.

**Why**: Minor, but the learner's mental model benefits from accurate framing. Four skills, not three: filtering/splitting, `conv`, `gcongr`, reindexing.

**Where**: L01 introduction.

**Effort**: Low (edit one sentence)
**Recommend**: Consider

---

### 11. L06 uses `Nat` throughout — `gcongr` is not shown working on `Int` or general ordered types

**What**: L06's `gcongr` example uses `Nat → Nat` functions. The learner may think `gcongr` is specific to natural numbers. A brief note (or a second example in the conclusion) showing it works for any ordered additive monoid would prevent this misconception.

**Why**: `gcongr` will be needed in W19 (binomial theorem context, possibly with integers or rationals). If the learner's mental model ties it to `Nat`, they may not think to use it elsewhere.

**Where**: L06 conclusion.

**Effort**: Low (sentence in conclusion)
**Recommend**: Consider

---

### 12. The `smul_eq_mul` rewrite in L09 is never introduced or explained

**What**: The boss proof uses `rw [Finset.sum_const, Finset.card_range, smul_eq_mul]` twice. The `smul_eq_mul` lemma converts `n • x` to `n * x`, which is necessary because `sum_const` returns a `smul` expression. But `smul_eq_mul` is never introduced or explained anywhere in this world. The learner encounters it only in the boss hints.

**Why**: If a boss level introduces new lemmas that were not taught in earlier levels, the boss is no longer a "combine what you learned" exercise — it is teaching new material under pressure. The learner should have seen `smul_eq_mul` in an earlier level, or at least in L05 or a pre-boss level.

**Where**: Introduce `smul_eq_mul` in an earlier level. Ideally, add it to whatever level first uses `sum_const` (which appears to be from W15). If it cannot be added to W15, introduce it in a pre-boss warm-up level in this world. At minimum, add a `NewTheorem smul_eq_mul` declaration and a `TheoremDoc` entry.

**Effort**: Medium (add NewTheorem/TheoremDoc, potentially restructure)
**Recommend**: Yes

---

## Overall impression

**What the world does well**: The introduction-conclusion structure is consistently strong across all levels, with good transfer remarks connecting Lean formalization to paper notation. The `conv` introduction (L05) is well-scaffolded with a clear explanation of the `arg 2; ext i; rw` pattern. The five-obligation structure of `sum_nbij'` is carefully laid out in L07. The world covers a coherent topic arc (filter, split, interchange, rewrite-under-binder, monotonicity, reindex).

**The single most important improvement**: The boss level does not test the world's core material. It exercises `conv` + `sum_add_distrib` + `sum_const` + `mul_sum` — all of which are W15 skills, plus `conv` which is the only W16 skill used. Filtering (the topic of L01-L02), summation interchange (L04), and reindexing (L07-L08) are all absent from the boss. A boss that integrates the actual new skills taught in this world would be a substantial pedagogical improvement. The secondary concern is that four of the first four levels (L01-L04) are single-tactic proofs, which makes the opening feel like an API catalog rather than a world building proof fluency.
