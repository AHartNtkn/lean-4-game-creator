# W8 FinsetTransformations — Enrichment Review (Round 1)

## Ranked suggestions

### 1. L07 is a trivial one-liner that teaches no proof move — replace with a level that actually demonstrates image shrinking

**What**: L07 asks the learner to prove `(image f s).card <= s.card` by typing `exact Finset.card_image_le`. This is an `exact`-and-done level with zero proof work. The learner doesn't see *why* image shrinks, doesn't compute the actual image, and gains no skill.

**Why**: The world's promise is that the learner can "reason about membership in the resulting finsets" and the plan says this level teaches "non-injective image" and coverage item C4 (R). A single `exact` doesn't teach anything about non-injectivity. The learner should actually *see* the collision. A better level would have the learner prove something like `(Finset.image (· % 2) {0,1,2,3}).card = 2` or `(Finset.image (· % 2) {0,1,2,3}).card < ({0,1,2,3} : Finset Nat).card`, where they must compute the image and witness the strict inequality. Alternatively, have them prove that two elements map to the same output (the collision itself), then draw the cardinality consequence. The current level is the only place in the world where non-injectivity and cardinality interact, and it teaches nothing.

**Where**: L07 — rewrite the level.

**Effort**: Medium (rewrite one level's statement and proof).

**Recommend**: Yes.

---

### 2. Missing: a level where the learner proves non-membership in an image (the false-witness direction)

**What**: Add a level asking the learner to prove something like `7 ∉ Finset.image (· * 2) {1, 2, 3}`, requiring them to show no witness exists.

**Why**: L03 and L04 teach the positive direction of `mem_image` (provide a witness). L02 teaches the negative direction of `mem_filter` (show the conjunction fails). But the negative direction of `mem_image` — showing that *no* element of the source maps to the target — is never taught. This is a fundamentally different proof obligation from providing a witness: it requires a universally-quantified argument ("for all a in s, f(a) != b"). The filter/image parallel (both taught positively and negatively for filter, only positively for image) is asymmetric, and the missing direction is the harder, more instructive one. It would also naturally introduce `Finset.not_mem_image` or require the learner to work from `mem_image` via `intro h; rcases h with ...` and exhaustive case analysis.

**Where**: New level, between L04 and L05 (or between L04 and the current L05).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 3. The `rfl` substitution trick (`rcases ... with ⟨a, ha, rfl⟩`) is used in L08 but never isolated or taught

**What**: The boss level's hints introduce `rcases hx with ⟨a, ha, rfl⟩` as a pattern, but this is the first time the learner sees `rfl` used inside a `rcases` pattern to perform substitution. It should be introduced in an earlier level where the proof is simpler so the learner can focus on this one technique.

**Why**: The `rfl` substitution in `rcases` is genuinely novel — it is not `rfl` as a closing tactic (which the learner already knows), but `rfl` as a *pattern variable* that triggers rewriting. Using it for the first time inside a boss-level proof alongside filter/image composition creates cognitive overload. It should appear in a standalone level (perhaps as part of L04 or a new level between L04 and L05) where the proof is simple enough that the learner can focus on the new technique. The conclusion of L08 calls this "especially powerful" — if it's powerful enough to name, it's powerful enough to teach separately.

**Where**: Introduce in L04 (modify the proof to use `rcases ... with ⟨a, ha, rfl⟩` instead of splitting manually), or add a new level specifically isolating this pattern.

**Effort**: Medium (modify L04's solution and hints to teach `rfl`-in-rcases, then L08 can use it as a known tool).

**Recommend**: Yes.

---

### 4. L05 (`map` vs `image`) membership proof is identical to L03 — the level doesn't teach *what's different* about `map`

**What**: L05 introduces `Finset.map` but the proof exercise is membership (`4 ∈ s.map e`), which uses `mem_map` in exactly the same way as `mem_image`. The introduction discusses cardinality preservation (`card_map`), but the proof never uses it. Add a part or modify the statement so the learner actually uses `Finset.card_map` — e.g., prove `(s.map e).card = s.card` for a specific finset, or prove that image and map give the same result for an injective function.

**Why**: The entire pedagogical point of L05 is the *distinction* between `map` and `image`. The introduction explains the distinction beautifully (cardinality guarantee vs. inequality), but the exercise proves only membership, which is identical for both. The learner walks away having done the exact same proof shape as L03 and L05, and the claimed learning — "map preserves cardinality" — was only read, never practiced. A good option: make the statement prove both `(s.map e).card = s.card` and contrast it with L07's `card_image_le`. This connects L05 and L07 while giving the learner practice with `card_map`.

**Where**: L05 — modify the statement or add a second part.

**Effort**: Medium (modify one level).

**Recommend**: Yes.

---

### 5. Missing: the dual composition direction (image then filter) is discussed in L06's conclusion but never practiced

**What**: L06's conclusion mentions `Finset.filter_image` and the dual composition (image first, then filter), but the learner never does it. Add a level where the learner proves membership in `Finset.filter p (Finset.image f s)` — the proof shape starts with `mem_filter` (outermost), then `mem_image` (inner), which is the reverse of L06.

**Why**: The conclusion of L06 explicitly says "you could also image then filter" and states the proof shape would be different (start with `mem_filter` since filter is outermost). This is a named strategy ("outside-in") and both orderings should be practiced. Mentioning the dual without letting the learner try it is a missed opportunity — especially since the two compositions produce different proof shapes, which is the exact point the level is trying to make. This would also be a natural place to practice the `rcases ... with ⟨a, ha, rfl⟩` pattern (suggestion 3).

**Where**: New level after L06 (or expand L06 into a two-part level).

**Effort**: High (new level).

**Recommend**: Consider.

---

### 6. `simp` is not in the `DisabledTactic` list despite being in the course's standard disabled set

**What**: Every level disables `trivial decide native_decide aesop simp_all` but does NOT disable `simp`. Meanwhile, `simp` is used explicitly in the proofs (L01, L03, L04, L05, L06, L08). The MEMORY notes say the standard disabled set is `trivial decide native_decide simp aesop simp_all`.

**Why**: Per the project's own lessons-learned, `simp` should be in the disabled set to prevent bypass exploits. However, the proofs in this world *use* `simp` (with explicit lemma arguments, e.g., `simp [Finset.mem_insert, Finset.mem_singleton]`). This creates a tension: disabling `simp` would break the proofs as written. The real question is whether `simp [...]` with explicit lemmas should be the taught path, or whether an alternative approach (like direct `rw` or `Finset.mem_cons` chain) should be used for membership in small literal finsets. If `simp` is meant to stay enabled here, that's a deliberate choice — but it should be documented as such, and the learner should be warned that `simp` alone (without targeted lemmas) may close things they should work through manually.

**Where**: All levels — the `DisabledTactic` line.

**Effort**: Low (add `simp` to disabled list) or medium (if proofs need rewriting to use `rw` chains instead).

**Recommend**: Consider. (This may be a systemic issue being tracked separately; flagging for completeness.)

---

### 7. No "what if?" or misconception level for filter — the learner might falsely believe `filter` always produces a non-empty result

**What**: Both filter levels (L01, L02) work with predicates where the filter is non-empty. A learner might not realize that filtering with a predicate satisfied by nothing produces the empty finset. A level like "prove `Finset.filter (fun x => x > 10) {1,2,3,4,5} = ∅`" would calibrate this.

**Why**: Boundary cases are pedagogically important (the plan itself identifies boundary calibration as coverage item C9). Showing that `filter` can produce `∅` also connects to the cardinality story in L07 (filter bound) and previews the W9 cardinality world. It's a small, concrete "what if?" moment.

**Where**: New level after L02, or a note in L02's conclusion.

**Effort**: Low (a sentence in L02's conclusion) or medium (a new level).

**Recommend**: Consider.

---

### 8. L08 boss conclusion names proof moves from "W6/W7" but this is W8 — the cross-references should name FinsetOperations/specific worlds

**What**: The conclusion of L08 says `rcases` is "from W6/W7" — but the learner doesn't know numeric world designations. They know world *names*. References to prior worlds should use the world name (e.g., "the Finset Operations world").

**Why**: Small polish, but it matters for learner orientation. If the learner played worlds in a different order (the dependency graph may allow some branching) or doesn't remember the internal numbering, "W6/W7" is meaningless. Naming the worlds makes the cross-reference useful.

**Where**: L08 conclusion text.

**Effort**: Low (text edit).

**Recommend**: Yes.

---

### 9. Strategy naming: the "outside-in" composition strategy introduced in L06 deserves explicit articulation as a named proof move

**What**: L06's conclusion says "Always start with the outermost operation's membership lemma" and calls this "outside-in." This is a genuine named strategy that generalizes beyond filter/image — it applies to any nested finset expression (`(s ∪ t) ∩ u`, `filter p (image f s)`, etc.). It should be articulated more prominently, perhaps with a callout box or a one-sentence strategy statement that the learner can recall.

**Why**: This is exactly the kind of proof-move naming that the enrichment reviewer exists to catch. The strategy is stated but buried in the conclusion's flow. A learner who internalized "outside-in" as a named move would approach the boss (L08) with more confidence. The strategy also transfers backward — it retroactively explains the proof shape in W7 L04 (combining operations) and L09/L10 (distributivity and De Morgan, which both peel operations from outside in).

**Where**: L06 conclusion — rewrite to make "outside-in" a prominently named strategy.

**Effort**: Low (text revision).

**Recommend**: Consider.

---

### 10. `card_image_of_injective` is declared as `NewTheorem` in L07 but never used in any proof

**What**: L07 introduces `Finset.card_image_of_injective` via `NewTheorem` and discusses it in the conclusion, but no level in the world asks the learner to use it. It's a phantom inventory item — the learner sees it but never practices with it.

**Why**: Introducing a theorem in the inventory without ever requiring its use creates false confidence. The learner thinks they "know" `card_image_of_injective` because it's in their toolkit, but they've never applied it. Either remove it from `NewTheorem` (just mention it in the conclusion text) or add a level where the learner actually uses it — e.g., prove `(Finset.image Nat.succ {1,2,3}).card = 3` using `card_image_of_injective` and `Nat.succ_injective`. The latter option also connects nicely to L05's discussion of injective functions.

**Where**: L07 — either remove from `NewTheorem` or add a level that uses it.

**Effort**: Low (remove from NewTheorem) or high (add a level).

**Recommend**: Yes.

---

## Overall impression

The world has a clear pedagogical arc: filter membership (L01-L02), image membership (L03-L04), map as a variant (L05), composition (L06), cardinality effects (L07), and integration (L08). The introductions are well-written, the filter-vs-image comparison table in L03's conclusion is excellent, and the boss level genuinely integrates the world's tools. The "outside-in" strategy naming in L06 is a good pedagogical move.

The single most important improvement is **suggestion 1**: L07 is currently an empty-calorie level. The learner types `exact Finset.card_image_le` and learns nothing about why non-injective functions shrink images. This is the only level in the world that addresses the cardinality dimension of image/map, which is arguably the most mathematically interesting aspect of the topic. Making this level require actual reasoning about collisions and cardinality computation would significantly deepen the world's coverage of C4 (non-injective image). The closely related suggestion 10 (unused `card_image_of_injective`) could be addressed at the same time by splitting L07 into two levels: one where the learner proves cardinality equality for an injective function, and one where they witness strict shrinkage for a non-injective function.
