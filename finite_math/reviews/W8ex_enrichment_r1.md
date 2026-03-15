# W8_ex FinsetExploration -- Enrichment Review (Round 1)

**Reviewer**: enrichment-reviewer
**World**: W8_ex FinsetExploration (7 levels)
**Role**: Example world concretizing W5--W8 on {1,2,3,4,5}
**Predecessor**: W8 FinsetTransformations (8 levels)
**Plan reference**: PLAN.md lines 430--442

---

## Ranked suggestions

### 1. L07 Boss is reassembly, not integration -- it repeats earlier proofs verbatim

**What**: The boss level asks the learner to redo L03 (filter), L04 (image), L05 (powerset), and L06 (product) as four independent subgoals joined by conjunction. The proofs are literally copy-pasted from those levels -- there is no new reasoning, no interaction between the parts, and no moment where the learner must combine two operations.

**Why**: A boss should test whether the learner can *integrate* skills, not whether they can repeat four earlier proofs in sequence. The current boss is four independent exercises stapled together. A genuine integration task would ask the learner to compose operations (e.g., filter then image then cardinality, or product then filter) and produce a single chain of reasoning. The W3_ex boss (FinThreeExamples L11) integrated injectivity, surjectivity, and cardinality in a single argument -- that is the standard to match.

**Where**: L07 (complete redesign)

**Effort**: High (new level statement and proof)

**Recommend**: Yes

**Suggested replacement**: A statement that chains multiple operations, for example: "Prove that the image of the even elements of {1,2,3,4,5} under the squaring function has 2 elements" -- this requires filter (select evens: {2,4}), image (square them: {4,16}), and cardinality (count: 2). The learner must compose filter, image, and cardinality in a single proof, requiring all the tools from L02--L06 to interact.

---

### 2. Missing: a level where image produces collisions on {1,2,3,4,5}

**What**: L04 shows squaring on {1,2,3,4,5}, which is injective (no collisions). The world never shows what happens when a non-injective function is applied to this specific finset, even though W8 L07 taught `card_image_le` precisely for this case.

**Why**: W8 L07's lesson (image can shrink cardinality) is a key insight, and an example world is the ideal place to concretize it. Squaring on {1,...,5} is injective and thus fails to illustrate the phenomenon. A concrete example like `fun x => x % 3` on {1,2,3,4,5} produces image {0,1,2} -- 3 elements from 5 inputs. This makes the abstract inequality visceral.

**Where**: New level between L04 and L05 (or modify L04 to be a two-part exercise)

**Effort**: Medium (new level, but the proof pattern is already established)

**Recommend**: Yes

---

### 3. L07 (transfer level from plan) is missing -- the world has no transfer moment

**What**: The plan specifies L07 as "Transfer: Describe in words what `filter`, `image`, and `powerset` do to a finite set" with coverage items T8 (S) and T1 (S). The implemented L07 is a boss level that does cardinality computations. There is no level in the world that asks the learner to articulate these operations in plain language.

**Why**: Transfer is one of the five layers. The plan explicitly assigns T8 (S) and T1 (S) to this world. The current conclusion of L07 contains transfer-like prose, but the learner is never asked to produce the transfer themselves. In W3_ex, L06 was a dedicated transfer level. This world should have one too.

**Where**: The boss conclusion contains some transfer prose, but a dedicated transfer level (or a transfer component in the boss) is needed.

**Effort**: Medium (add a transfer question to the boss intro/conclusion, or add a dedicated level)

**Recommend**: Yes

---

### 4. L01 proof is extremely long for what it teaches -- the `ext`/`simp`/`omega`/witness chain is daunting

**What**: L01's second subgoal (range+image = literal) requires `ext`, `simp only` with four lemmas, `constructor`, `rintro` with angle-bracket destructuring, `omega`, and a pattern-match witness construction. This is the most complex proof in the world, and it appears in the very first level.

**Why**: Example worlds should build confidence through concreteness. A learner who just finished W8 knows `ext`, `mem_image`, and `simp`, but the L01 backward direction -- `rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩` -- is extremely dense. The first level of an example world should be welcoming, not the hardest proof. Consider simplifying: (a) use `decide` or `native_decide` for the second part if the DisabledTactic list allows it, or (b) split into two separate levels (L01a: iterated insert = literal via `rfl`; L01b: range+image = literal via `ext`).

**Where**: L01

**Effort**: Medium (split into two levels, or simplify the proof)

**Recommend**: Consider

---

### 5. No level addresses `Finset.range` membership concretely

**What**: L01 introduces `Finset.range` and includes a `DefinitionDoc` for it, but no level asks the learner to prove a membership fact about `Finset.range` directly (e.g., `3 ∈ Finset.range 5`). The range is only used inside an image composition.

**Why**: `Finset.range` is one of the new definitions introduced in this world (`NewDefinition Finset.range`). The plan's L01 description says the learner should "Construct {1,2,3,4,5} using ... `Finset.range 5`." But the learner never works with `Finset.range` on its own -- they only see it through the lens of `image`. A quick membership check (`3 ∈ Finset.range 5` via `Finset.mem_range`) would ground the definition before it is composed with `image`.

**Where**: New level between L01 and L02, or a subgoal within L02

**Effort**: Low-medium (small additional level or extra subgoal)

**Recommend**: Consider

---

### 6. L02 both subgoals solved by the same `simp` call -- missed opportunity for manual proof

**What**: Both `3 ∈ {1,2,3,4,5}` and `6 ∉ {1,2,3,4,5}` are solved by `simp [Finset.mem_insert, Finset.mem_singleton]`. The learner does the same thing twice.

**Why**: The membership level could differentiate the two tasks: solve the positive case manually (peel off inserts with `rw [Finset.mem_insert]`, choose `Or.inr`, repeat until `rfl`) and the negative case with `simp`. This would reinforce the manual membership reasoning from W6 while showing that `simp` automates the same process. The contrast between manual and automated approaches is a teaching moment that W6 L05 ("simp vs manual rewriting") already established -- this is an ideal retrieval opportunity.

**Where**: L02 (modify first subgoal to require manual proof)

**Effort**: Low (change proof and hints for one subgoal)

**Recommend**: Consider

---

### 7. L05/L06 introduce powerset and product as "previews" but the learner never touches membership

**What**: L05 proves a cardinality fact about `powerset` using `card_powerset` + `rfl`. L06 proves membership in a product using `mem_product` and cardinality using `card_product`. But for powerset, the learner never proves a membership fact (e.g., `{1,3} ∈ {1,2,3}.powerset`). The `mem_powerset` lemma is documented but never used.

**Why**: The plan says this level covers "Concretization of powerset" with coverage item E8 (I). A cardinality computation is not full concretization -- the learner should also see a concrete subset membership in the powerset. Adding a subgoal like `{1,3} ∈ ({1,2,3} : Finset Nat).powerset` (proved via `Finset.mem_powerset` + subset reasoning) would give the learner hands-on experience with the membership structure, not just the counting formula.

**Where**: L05 (add a second subgoal)

**Effort**: Low (add one conjunction arm)

**Recommend**: Yes

---

### 8. L03/L04 conclusions could name the "ext + simp + decision" proof strategy

**What**: L03 and L04 both use the pattern `ext x; simp only [...]; omega/case analysis`. The conclusion of L03 describes the three steps, and L04's conclusion describes the two-direction pattern. Neither names this as a reusable strategy.

**Why**: This `ext` + membership simplification + arithmetic/witness strategy is the workhorse of concrete finset equality proofs. It will reappear in W9 and beyond whenever the learner needs to identify a computed finset. Naming it (e.g., "the ext-simp-decide pattern" or "the membership reduction strategy") would help the learner recognize it as a transferable tool rather than three ad-hoc steps.

**Where**: L03 or L04 conclusion (add a sentence naming the strategy)

**Effort**: Low (one sentence in conclusion text)

**Recommend**: Yes

---

### 9. L06 product level does not compute the actual elements

**What**: L06 proves `(1,4) ∈ {1,2} ×ˢ {3,4}` and the cardinality formula. The conclusion lists all four pairs `(1,3), (1,4), (2,3), (2,4)` in prose, but the learner never proves that one of the "unexpected" pairs (like `(2,3)`) is also in the product, or that a pair like `(3,1)` is NOT in the product.

**Why**: A non-membership fact (`(3,1) ∉ {1,2} ×ˢ {3,4}`) would reinforce the component-wise nature of product membership and prevent the misconception that the product is commutative (i.e., that `{1,2} ×ˢ {3,4}` contains `(3,1)`). This is a concrete counterexample opportunity.

**Where**: L06 (add a third conjunction arm)

**Effort**: Low (add one subgoal)

**Recommend**: Consider

---

### 10. World introduction (L01) could connect to mathematical practice of "running examples"

**What**: L01's introduction says "Instead of learning new theory, you will work with a single finset" but does not explain *why* mathematicians work with running examples.

**Why**: The pedagogical purpose of example worlds is itself a lesson. A sentence like "Mathematicians often test their understanding of new definitions by working through a single concrete example, checking that abstract theorems produce the expected answers. This is the mathematical practice of concretization." would elevate the world from "drill" to "deliberate practice." W3_ex's L01 had this framing explicitly ("This is the mathematical practice of **concretization**: making abstract definitions tangible by grounding them in specific, small cases").

**Where**: L01 introduction (add 1-2 sentences)

**Effort**: Low (prose addition)

**Recommend**: Consider

---

## Overall impression

The world does a solid job of walking the learner through each finset operation on a concrete example. The level sequence follows the natural order (build, membership, filter, image, powerset, product, boss), the conclusions include good plain-language transfer statements, and the table-based summaries in the conclusions are effective. The `DisabledTactic` set is consistent across all levels.

The single most important improvement is **redesigning the boss level** (suggestion 1). The current boss is four independent exercises joined by `And` with no interaction between the parts. An example world's boss should ask the learner to compose operations, demonstrating that the individual skills combine into something greater. The second-highest priority is **adding a non-injective image level** (suggestion 2), which would concretize W8 L07's lesson about cardinality shrinkage -- without it, the example world fails to cover one of the most important insights from the predecessor.
