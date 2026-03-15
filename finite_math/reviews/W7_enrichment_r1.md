# W7 FinsetOperations — Enrichment Review (Round 1)

## Ranked suggestions

### 1. The `simp` membership shortcut is never demonstrated — yet the transfer moment references it

**What**: The plan's transfer moment says "That's exactly what `ext` + `simp` does." But in the actual world, `simp` is never used inside an `ext` proof. Every `ext` proof (L05, L06, L09, L10) manually rewrites with `mem_union`/`mem_inter`/`mem_sdiff` and manually destructs. Add a level (or modify L06's conclusion) that shows `simp [Finset.mem_union]` or `simp [Finset.mem_inter, Finset.mem_union]` closing the biconditional in one shot after `ext`.

**Why**: This is a genuine gap between what the world teaches and what the world claims. The learner finishes L10 having never seen `simp` used inside an `ext` proof, yet the conclusion tells them `ext + simp` is the idiomatic pattern. More practically, the manual approach taught here becomes unsustainable at the complexity of L09-L10 (the distributivity proof is 40+ tactic steps). Showing the learner that `simp` can automate the membership chasing after `ext` is both honest and empowering — it lets them see the manual steps as understanding and the `simp` shortcut as fluency.

**Where**: Best as a new level between L06 and L07 (call it "L06b: ext + simp shortcut"). Reprove union commutativity (same statement as L05) but this time with `ext a; simp [Finset.mem_union, or_comm]`. Then in the conclusion, contrast the two approaches: L05's manual proof showed you what's happening; this proof shows the tool that automates it. Alternatively, add this as a second statement within L06 or as a remark in L06's conclusion.

**Effort**: Medium (new level or substantial modification to L06)

**Recommend**: Yes

---

### 2. No level addresses a false generalization or converse

**What**: Add a level that shows a natural-but-false claim related to the operations taught. The most natural candidate: the converse of subset-union (`s ⊆ s ∪ t` is true, proved in L07 — but `s ∪ t ⊆ s` is false in general). Alternatively: `s \ t = t \ s` is false, or `s ∩ t = s` does not imply `t ⊆ s` (wait — it does imply `s ⊆ t`). The cleanest option: ask the learner to prove `s \ t ≠ t \ s` for specific `s, t` where this fails, or prove `¬ (∀ s t : Finset Nat, s \ t = t \ s)` by providing a counterexample.

**Why**: The world proves seven positive facts and zero negative ones. Every operation is introduced with "here's the truth," but the learner never encounters "here's what goes wrong." A counterexample level builds the habit of testing conjectures — critical for mathematical maturity. The plan's misconception map doesn't list any misconception for W7, which itself is a gap: learners can and do wrongly assume set difference is symmetric.

**Where**: After L07 (subset) and before L08 (by_cases). A short level: "Prove that `{1, 2, 3} \ {2, 3} ≠ {2, 3} \ {1, 2, 3}` — set difference is not symmetric." The proof would use `intro h`, then `have` a membership contradiction (e.g., `1 ∈ {1, 2, 3} \ {2, 3}` but `1 ∉ {2, 3} \ {1, 2, 3}`).

**Effort**: Medium (new level)

**Recommend**: Yes

---

### 3. The introduction's internal monologue in L08 should be removed

**What**: L08's introduction contains a false start where the author considers a different task ("Actually, for this level you do NOT need `by_cases` -- this is a warm-up. But the next level will use it. Wait -- let's make this level actually use `by_cases`. Here is a better task:"). This reads as draft notes that were not cleaned up. Remove the false start and present the actual task directly.

**Why**: This is not an enrichment suggestion in the strict sense — it's an authorial artifact that undermines the world's polish. A learner reading "Wait -- let's make this level actually use `by_cases`" will be confused about whether they missed something. The introduction should present the task confidently.

**Where**: L08, introduction text (lines 36-54 of the file)

**Effort**: Low (text edit)

**Recommend**: Yes

---

### 4. No `Finset.subset_iff` or `Finset.Subset.antisymm` theorem documentation

**What**: L07 introduces the subset proof pattern but does not declare a `NewTheorem` for `Finset.subset_iff` or provide a `TheoremDoc` for it. The level mentions the theorem in the introduction but doesn't add it to the learner's inventory. Similarly, the world introduces `⊆` but never mentions that `⊆` + `⊇` gives equality (subset antisymmetry), which is the alternative to `ext` for proving finset equality.

**Why**: The learner encounters `⊆` in this world and will use it again in W8+ (e.g., filter gives a subset). Without the theorem in the inventory, they won't be able to look it up. The missing antisymmetry mention is also a mathematical depth opportunity: the world teaches two ways to prove equality (ext, and now subset in both directions) but only names the first.

**Where**: L07 — add `NewTheorem Finset.subset_iff` and a `TheoremDoc`. In the conclusion, add a sentence: "There's another way to prove finset equality: show `s ⊆ t` and `t ⊆ s`. This is called **antisymmetry of subset**. We won't need it in this world (since `ext` is more direct), but it's a useful pattern to know."

**Effort**: Low (add NewTheorem/TheoremDoc + a sentence in conclusion)

**Recommend**: Yes

---

### 5. The "membership triple" proof pattern is used repeatedly but never named

**What**: Levels L05, L06, L09, and L10 all follow the same three-step pattern inside each direction of an `ext` proof: (1) `intro h`, (2) rewrite `h` with a `mem_*` lemma, (3) `rcases h`. This pattern is used 8+ times across the world but is never given a name. Call it the "membership chase" or "unpack-and-rebuild" pattern.

**Why**: Naming a proof pattern makes it transferable. The learner is doing the same thing over and over but may not realize it's the same move. Giving it a name in L06's conclusion ("Notice you've now used the same three-step 'membership chase' twice...") means the learner can invoke it as a concept in L09 and L10, rather than re-deriving it each time. This also sets up W8, where `mem_filter` and `mem_image` will require the same pattern.

**Where**: L06 conclusion (where the "recipe" is already partially articulated — lines 89-97). Make the existing recipe more prominent and give it a name. Then reference the name in L09 and L10.

**Effort**: Low (text additions to conclusions)

**Recommend**: Yes

---

### 6. Union and intersection associativity are missing

**What**: The world proves commutativity for both union (L05) and intersection (L06), but neither associativity is proved or even mentioned. `(s ∪ t) ∪ u = s ∪ (t ∪ u)` is a natural companion to commutativity, and the proof requires a different `rcases` pattern (three-way disjunction or nested destructuring).

**Why**: Commutativity and associativity are the two basic algebraic laws for any binary operation. Proving commutativity without associativity is like teaching addition without mentioning that `(a + b) + c = a + (b + c)`. More importantly, the associativity proof introduces a new proof shape: the three-way `rcases h with (hs | ht) | hu` pattern for nested disjunctions, which is a genuine new skill. The learner will need this in W8+ when reasoning about nested operations.

**Where**: A new level after L06 (call it "L06b: union associativity"). The proof would use `ext a`, then in each direction `intro h`, `rw [Finset.mem_union] at h` (twice, on nested unions), `rcases` the nested disjunction, and rebuild.

**Effort**: High (new level)

**Recommend**: Consider

---

### 7. L01-L03 use concrete finsets but L04 could have used abstract ones

**What**: L04 uses concrete finsets (`{1,2,3}`, `{3,4,5}`, `{2,3}`). Since L05 transitions to abstract finsets, L04 is the last concrete-finset level before the abstraction jump. Consider making L04 use abstract finsets (like L05+), which would make the transition smoother.

**Why**: The jump from concrete finsets in L04 to abstract finsets in L05 is abrupt. In L04, the learner still closes goals with `simp [Finset.mem_insert, Finset.mem_singleton]`. In L05, `simp` is no longer applicable because the finsets are abstract. Making L04 abstract would ease this transition by showing that the `rw [mem_*]` steps work on abstract finsets too, while the `simp` closure does not.

**Where**: L04

**Effort**: Medium (rewrite the level statement and proof)

**Recommend**: Consider

---

### 8. The boss (L10) forward direction uses an indirect argument that could be named

**What**: In L10's forward direction (lines 60-84), the learner proves `a ∉ u` from `a ∈ t` and `a ∉ t ∩ u` by assuming `a ∈ u`, building `a ∈ t ∩ u`, and contradicting `hntu`. This is a proof by contradiction / contraposition move that is never named or highlighted.

**Why**: This is the first time in the world (and possibly the course so far) that the learner must prove a negative statement by assuming the positive and deriving a contradiction. The conclusion mentions "negation reasoning" in passing (line 145-146) but doesn't isolate the pattern: "To prove `a ∉ X`, assume `a ∈ X` and derive a contradiction." This is a fundamental proof move that will recur throughout mathematics.

**Where**: L10 introduction or conclusion — add a paragraph explaining the negation proof pattern. Or better, add a dedicated hint in the proof at the point where `intro hu; apply hntu` happens, explaining: "To prove `a ∉ u`, we introduce the assumption `a ∈ u` (calling it `hu`) and then show this leads to `a ∈ t ∩ u`, which contradicts `hntu`."

**Effort**: Low (enhanced hint text + conclusion paragraph)

**Recommend**: Yes

---

### 9. Cross-world foreshadowing for W8 (filter) and W9 (cardinality) is minimal

**What**: The conclusion of L10 says "In the next world, you will learn to filter finsets by predicates, map functions over finsets, and reason about membership in the resulting finsets." This is a bare preview. Add a sentence connecting the current world's tools to what comes next: "The `ext` + membership-lemma pattern you mastered here is the same pattern you'll use with `mem_filter` and `mem_image` in the next world. The only difference is the membership lemma."

**Where**: L10 conclusion

**Effort**: Low (sentence addition)

**Recommend**: Consider

---

### 10. `iff` tactic (`constructor` for biconditionals) could be mentioned alongside `constructor`

**What**: The world uses `constructor` to split biconditionals after `ext`. In Lean 4, `constructor` works for `Iff` because `Iff` is a structure with two fields. But the world never explains *why* `constructor` works on `↔` goals — it just says "use `constructor` to split." A one-sentence explanation ("The biconditional `↔` is a pair of implications, so `constructor` splits it into the forward and reverse directions, just like it splits `∧` into its two components") would help.

**Why**: Without this explanation, the learner may not understand the connection between `constructor` on `∧` (which they learned in L02) and `constructor` on `↔` (which appears in L05). Making the connection explicit reinforces that `constructor` is a general tool for splitting structure goals.

**Where**: L05 introduction, near line 34 where `constructor` is introduced for biconditionals.

**Effort**: Low (sentence addition)

**Recommend**: Consider

---

## Overall impression

The W7 FinsetOperations world is structurally sound. The level ladder follows a clean progression from individual operation membership lemmas (L01-L03) through combination (L04), extensionality (L05-L06), subset (L07), case analysis (L08), and two integration levels (L09-L10). The boss level is genuinely challenging and integrates every tool taught. The hints are thorough and the conclusions provide good transfer-to-paper-proof connections.

The single most important improvement is **Suggestion 1**: demonstrating `simp` inside an `ext` proof. The world's transfer moment promises that `ext + simp` is the idiomatic workflow, but no level actually shows this. The learner grinds through 40+ manual tactic steps in L09-L10 without ever seeing the automation that makes these proofs practical. Adding a short level that reproves a commutativity result with `ext a; simp [...]` would close this gap, give the learner a moment of "oh, all that work can be automated," and make the transfer moment honest. The runner-up is **Suggestion 3** (cleaning up the draft notes in L08's introduction), which is a simple fix that noticeably improves polish.
