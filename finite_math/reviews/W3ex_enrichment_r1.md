# Enrichment Review: W3_ex (FinThreeExamples) -- R1

**Reviewer**: enrichment-reviewer (first review)
**World**: FinThreeExamples (6 levels)
**Position**: After FinIntro (W1, 13 levels) and FinCompute (W2, 11 levels); before ListBasics (W3)
**World type**: Example world -- concretize Fin on the specific object Fin 3

---

## Ranked suggestions

### 1. Missing: a level where `fin_cases` is used structurally (not just `decide`)

**What**: Add a level that requires the learner to prove a property of Fin 3 by `fin_cases` with per-case reasoning, not by `decide` alone.

**Why**: This is the single most important gap. Every level in this world is solved by a one-tactic proof (`decide`, `norm_num`, or `exact`). The learner never actually does case analysis on Fin 3 -- the tactic that FinCompute (W2) spent its first four levels teaching. An example world should exercise prior theory, not just invoke decision procedures. The plan's coverage table assigns V2 (case exhaustion on Fin) an "R" (retrieval) tag for W3_ex, but no level in the world actually retrieves this skill. The learner who completes W3_ex has pressed `decide` four times, `norm_num` once, and `exact` once. They have not concretized their understanding of Fin 3 by doing anything non-trivial with its elements.

A good candidate: prove that every element of Fin 3 satisfies `i.val * i.val <= 2 * i.val` (which is true for 0, 1, 2 but requires checking each case). Or prove that the function `fun i : Fin 3 => 2 * i` is not the identity by finding a specific counterexample (`i = 2` gives `4 mod 3 = 1`, not 2). The point is to force the learner to engage with the structure of Fin 3 rather than delegating to an oracle.

**Where**: New level, ideally inserted between L01 (Enumerate) and L02 (FunctionOnFin3), or between L02 and L03.

**Effort**: High (new level)

**Recommend**: Yes -- this is the most impactful single change. Without it, the world fails its own stated purpose of "concretizing Fin 3."

---

### 2. L02 duplicates FinCompute L08 almost exactly

**What**: Replace L02 (FunctionOnFin3) with a genuinely different computation that exercises a different mathematical idea, or at minimum rephrase the statement so it is not a near-copy of FinCompute L08.

**Why**: FinCompute L08 already proves `(0 : Fin 3).val ^ 2 + 1 + ((1 : Fin 3).val ^ 2 + 1) + ((2 : Fin 3).val ^ 2 + 1) = 8` using `norm_num`. W3_ex L02 proves the same arithmetic identity with the same function, the same values, and the same tactic, just with a slightly different statement encoding (using anonymous lambda applications instead of explicit `.val` calls). This is not retrieval on a fresh surface -- it is the same surface. A learner who just completed FinCompute will feel that W3_ex is wasting their time.

A replacement could compute something structurally different: the maximum of a function on Fin 3 (e.g., show that the maximum of `fun i => i.val ^ 2` over Fin 3 is 4), or show that a specific function on Fin 3 is a bijection (connecting to L04/L05's injection/surjection theme), or compute a sum using `Finset.sum` notation if that notation is previewed here (the conclusion already mentions `Finset.sum` as a future concept).

**Where**: L02

**Effort**: Medium (rewrite one level)

**Recommend**: Yes

---

### 3. L04 does not actually prove injectivity of a function on Fin 3 -- it uses Fin 3 -> Fin 5

**What**: The level title says "Injectivity on Fin 3" but the actual statement is about `Fin.castSucc ∘ Fin.castSucc : Fin 3 -> Fin 5`, which maps into a much larger codomain. Consider adding or replacing with a genuine Fin 3 -> Fin 3 injection (i.e., a bijection), which would teach the learner that an injective function from a finite set to itself must be surjective.

**Why**: An injection from a 3-element set to a 5-element set is too easy to be interesting -- of course distinct inputs map to distinct outputs when the codomain is much larger than the domain. The real insight about injectivity on finite types is the pigeonhole constraint: an injection from Fin 3 to Fin 3 must hit every element (it is automatically surjective). This is a theorem the learner should see concretely before encountering it abstractly in the pigeonhole world (W12). Even if the formal theorem is deferred, the intuition should be planted here.

A concrete example: prove that the function sending 0->1, 1->2, 2->0 (cyclic permutation) is injective, using `decide`. Then in the conclusion, point out that it is also surjective -- and ask the learner to think about whether this is a coincidence. This seeds vocabulary for W12 (counting/pigeonhole) and W22 (permutations).

**Where**: L04, or new level after L04

**Effort**: Medium (modify L04 or add a new level)

**Recommend**: Yes

---

### 4. The injectivity/surjectivity pair misses the converse direction

**What**: L04 shows injectivity (Fin 3 -> Fin 5) and L05 shows non-surjectivity (Fin 3 -> Fin 4). But the natural companion -- a function from Fin 4 to Fin 3 that IS surjective but NOT injective -- is absent.

**Why**: The pair as currently written tells half the pigeonhole story: a function from a smaller set to a larger set can be injective but cannot be surjective. The other half -- a function from a larger set to a smaller set can be surjective but cannot be injective -- is equally important and completes the conceptual picture. Without it, the learner sees injectivity and surjectivity as unrelated properties rather than as dual constraints governed by cardinality. A concrete surjection `Fin 4 -> Fin 3` (e.g., `fun i => if i = 3 then 0 else i.castSucc`, or simply mapping by `i mod 3`) would make this vivid.

**Where**: New level between L05 and L06, or modify L05 to include both directions.

**Effort**: High (new level) or medium (extend L05 conclusion to mention the dual and add a second statement)

**Recommend**: Yes

---

### 5. L03 (PairingElements) is mathematically trivial and teaches no reusable skill

**What**: Strengthen L03 so that it asks the learner to prove a property of the product type, not just construct an element.

**Why**: The level asks the learner to type `exact (2, 1)`. That is not a proof move, it is not a computation, it is not a verification -- it is a term construction that any learner who completed FinIntro can do without thinking. The conclusion mentions the multiplication principle (`3 * 3 = 9`) but the level never proves it. The level introduces product types but does not exercise them.

Better alternatives:
- Prove `Fintype.card (Fin 3 x Fin 3) = 9` using `decide`. This makes the multiplication principle concrete.
- Prove that two specific pairs are not equal: `((0 : Fin 3), (1 : Fin 3)) != ((1 : Fin 3), (0 : Fin 3))`. This teaches that pair order matters and previews the distinction between ordered and unordered pairs that surfaces in combinatorics (W17+).
- Prove that a specific element is in `Finset.univ` for the product type (previewing `Finset.univ`).

Any of these would be more instructive than `exact (2, 1)`.

**Where**: L03

**Effort**: Medium (rewrite one level)

**Recommend**: Yes

---

### 6. L06 (Transfer) is labeled as a transfer level but proves a fact about Fin 0, not Fin 3

**What**: The transfer level should actually be about Fin 3 -- summarizing the world's lessons -- rather than proving `forall i : Fin 0, False`, which is a Fin 0 fact already covered in FinIntro L05.

**Why**: The plan says the transfer level should "state in words what Fin 3 represents and why Fin 0 is empty." The "state in words" part is entirely in the conclusion text -- the actual proof obligation is about Fin 0, which was already covered in FinIntro. A proper transfer level for this world would ask the learner to do something that requires synthesizing what they learned about Fin 3 specifically.

Better alternatives:
- Prove `Fintype.card (Fin 3) + Fintype.card (Fin 0) = 3` (connecting the two boundary cases).
- State and prove that every function `Fin 3 -> Fin 3` that is injective is also surjective (a concrete instance of the pigeonhole principle, previewing W12).
- Prove that the identity function on Fin 3 is both injective and surjective (tying together L04 and L05).
- Ask the learner to prove a plain-language equivalence: that `Fin 3` is equivalent to `{0, 1, 2}` as a finset, connecting Fin to Finset (previewing Module C).

The current level also duplicates FinIntro L05 (`Fin 0 -> False`), which means the world ends with a repeated exercise from two worlds ago.

**Where**: L06

**Effort**: Medium (rewrite one level)

**Recommend**: Yes

---

### 7. Missing: modular arithmetic on Fin 3

**What**: Add a level that exercises modular arithmetic on Fin 3, connecting to FinCompute W2 L07-L09.

**Why**: FinCompute devoted three levels (L07, L08, L09) to modular arithmetic on Fin n. The example world should concretize this on Fin 3, which has particularly interesting modular arithmetic properties (it is the smallest nontrivial cyclic group under addition). For example: prove that `(2 : Fin 3) + (2 : Fin 3) = (1 : Fin 3)` (wrapping), or that `(1 : Fin 3) + (1 : Fin 3) + (1 : Fin 3) = 0` (the order of 1 in Z/3Z). This would naturally connect Fin 3 to the algebraic_structures course (Course 4) that follows.

The conclusion could point out that Fin 3 with addition forms a cyclic group of order 3, seeding vocabulary for the algebraic_structures course.

**Where**: New level, ideally after L01 or L02.

**Effort**: High (new level)

**Recommend**: Consider -- valuable for cross-course foreshadowing, but the world may already need expansion for higher-priority items.

---

### 8. No level uses `Fin.val` extraction or the coercion arrow on Fin 3 elements

**What**: Add a level that requires the learner to extract `.val` from a Fin 3 element and reason about the underlying natural number.

**Why**: FinIntro devoted significant effort to teaching the coercion from Fin n to Nat (L02, L06, L07, L12). The example world should show this in action on Fin 3 -- for instance, prove that `(2 : Fin 3).val = 2`, or prove that for all `i : Fin 3`, `i.val < 3` (which is just `i.isLt` but makes the bound concrete). The current world never touches `.val` or the coercion arrow, which means the learner's understanding of the Fin-to-Nat bridge is not exercised.

**Where**: New level or integrate into L01.

**Effort**: Medium (modify L01 or add a new level)

**Recommend**: Consider

---

### 9. The world has no boss level

**What**: Add a boss level that integrates multiple skills from the world.

**Why**: The plan does not list a boss for W3_ex (the "Boss" column in the summary table shows "--" for this world). However, the quality standards (00_what_good_looks_like.md) emphasize that bosses should "integrate several moves learned in the world." An example world arguably does not need a traditional boss, but the current L06 is not doing the integration work either. If the world is expanded with suggestions 1, 3, 4, and 7, then a boss that asks the learner to combine case analysis, function evaluation, and injectivity/surjectivity reasoning on a single Fin 3 problem would provide satisfying closure.

Example boss: prove that there are exactly 6 bijections from Fin 3 to Fin 3 (i.e., `Fintype.card (Equiv.Perm (Fin 3)) = 6`). This is solvable by `decide`, but the conclusion could explain why: 3! = 6, and each permutation corresponds to a choice of where to send 0 (3 options), then 1 (2 options), then 2 (1 option). This previews factorials (W17) and permutations (W22).

**Where**: New level at the end (replacing or supplementing L06)

**Effort**: High (new level)

**Recommend**: Consider -- depends on whether the world is expanded enough to warrant a boss.

---

### 10. The conclusion of L04 contains an error in the plain-language transfer

**What**: The conclusion says "f(i) = 2i is injective on {0,1,2}" but the actual function is `Fin.castSucc o Fin.castSucc`, which is the identity embedding (f(i) = i), not f(i) = 2i.

**Why**: This is a factual error that will confuse the learner. The function maps 0->0, 1->1, 2->2 (identity embedding into Fin 5), not 0->0, 1->2, 2->4. The transfer paragraph must match the actual mathematics of the level.

**Where**: L04, conclusion text.

**Effort**: Low (fix one sentence)

**Recommend**: Yes

---

### 11. Cross-world foreshadowing is generic rather than specific

**What**: Make the foreshadowing in conclusions point to specific future levels/worlds by name, not just "later worlds."

**Why**: Multiple conclusions say things like "in later worlds, you will learn Finset.sum" or "you will study [the pigeonhole principle] formally in a later world." These are vague. The plan has specific world names and numbers for these concepts. Saying "In World 13, you will learn `Finset.sum`" or "In World 12, you will see the full pigeonhole principle" gives the learner a concrete sense of the course structure and builds anticipation. The RealAnalysisGame patterns reference (01_patterns_from_existing_games.md) emphasizes that narrative is curriculum -- specific forward references are more motivating than vague ones.

**Where**: Conclusions of L02, L03, L05

**Effort**: Low (edit conclusion text)

**Recommend**: Consider

---

### 12. Missing: a "what if" level exploring what breaks when n changes

**What**: Add a level that asks the learner to think about what happens when `Fin 3` is replaced by `Fin 2` or `Fin 4` -- for instance, prove that `Fintype.card (Fin 2) = 2` and compare with the Fin 3 result.

**Why**: The "what if" category of pedagogical opportunities is about building mathematical maturity through parameter variation. An example world centered on Fin 3 could briefly show how properties change when n changes. For instance: the surjectivity failure in L05 depends on `3 < 4`. What if the codomain were Fin 3 instead of Fin 4? Then surjectivity could succeed. Showing this contrast makes the role of cardinality in injectivity/surjectivity arguments visible.

**Where**: Could be integrated into L05's conclusion or as a new level.

**Effort**: Low (conclusion text) to High (new level)

**Recommend**: Consider

---

## Overall impression

The world has a sensible arc: enumerate Fin 3, compute with a function on it, build pairs, test injectivity, show surjectivity fails, and transfer. The conclusions are well-written and consistently include plain-language translations, which is a strength. The world correctly previews pigeonhole and product-type counting, and the introduction to L01 does a good job of framing the world's purpose.

The single most important improvement is **adding a level that requires `fin_cases` or other non-trivial reasoning** (Suggestion 1). As it stands, every level is solved by a single tactic (`decide`, `norm_num`, or `exact`), which means the world is a sequence of button-presses rather than a sequence of learning moments. An example world's purpose is to make abstract theory tangible through hands-on computation -- but "hands-on" requires the learner to actually do something, not just invoke an oracle. The world currently tests whether the learner knows that `decide` exists, which was already the lesson of FinCompute L03. It does not test whether the learner understands Fin 3.

Secondary priorities are fixing the factual error in L04's conclusion (Suggestion 10), replacing the near-duplicate L02 (Suggestion 2), and adding the missing dual direction for the injectivity/surjectivity pair (Suggestion 4). Together, these changes would transform the world from a perfunctory example pass into a genuine concretization experience.
