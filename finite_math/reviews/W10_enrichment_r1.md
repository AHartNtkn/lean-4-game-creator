# W10 FinsetInduction — Enrichment Review (Round 1)

## Ranked suggestions

### 1. L05 teaches `by_cases` on membership but not `card_insert_of_notMem` applied in the inductive step — the plan's Level 5 ("cardinality-by-induction") is missing

**What**: The plan calls for L05 to be "a cardinality-by-induction proof" that combines V4 with M9. The implemented L05 (`CardInsertLe`) is a `by_cases` proof that never uses finset induction at all. The plan's intended lesson — using `Finset.induction_on` to prove a cardinality result where the inductive hypothesis is meaningfully used in combination with `card_insert_of_notMem` — is absent from the world. (A stale file `L05_CardinalityByInduction.lean` exists but is not imported.)

**Why**: This is the world's single biggest gap. Levels L01-L04 set up finset induction, L06 introduces `card_le_card` as a black-box lemma, L07-L08 are comparison/refine levels, and L09 is the boss. There is no level between L04 and L09 where the learner actually performs a full finset induction with a cardinality goal and uses `ih` meaningfully to close an arithmetic subgoal. The boss asks them to do exactly this, but they have never practiced the pattern. L05 (as implemented) is a good level about `by_cases`, but it does not fill the gap.

**Where**: Replace or supplement the current L05 with a true "cardinality by induction" level. The `by_cases` content of the current L05 could be folded into L04 or kept as a separate level if the world is expanded to 10 levels.

**Effort**: High (adding or restructuring a level).

**Recommend**: Yes.

---

### 2. L06 presents `card_le_card` as a one-step `exact` — the learner never proves a subset-cardinality result by induction

**What**: L06 ("Subset implies card inequality") has the learner simply apply `Finset.card_le_card h` to a concrete example `{1, 2} ⊆ {1, 2, 3}`. The conclusion mentions that `card_le_card` is internally proved by finset induction, but the learner never sees or reproduces this argument. The plan marks this level as "V15 as a proof move" — but the proof move is just `exact`.

**Why**: This is a missed opportunity to show finset induction applied to a genuinely interesting mathematical result. The proof that `s ⊆ t → s.card ≤ t.card` by induction on `s` is an excellent exercise: the base case is `0 ≤ t.card`, the inductive step requires using `a ∈ t` (from `insert a s' ⊆ t` and `a ∈ insert a s'`) and relating `card (insert a s')` to `card s'`. This would give the learner a complete finset induction proof that uses `ih`, `ha`, and subset reasoning together — exactly the skills the boss demands.

**Where**: L06 should become a guided finset induction proof of `card_le_card` (disable the library lemma), not a one-step application. The current one-step version could be the first part ("here is the lemma") followed by "now prove it."

**Effort**: High (rewriting a level).

**Recommend**: Yes.

---

### 3. The world never names the "decompose-compute-reassemble" strategy pattern

**What**: Levels L03, L04, L05 (current), L07, L08, and L09 all follow the same proof shape in the insert case: (a) decompose `insert a s'` using a lemma like `card_insert_of_notMem`, (b) compute or bound the result, (c) close with `omega` or `rfl`. This three-step pattern is never articulated as a reusable strategy.

**Why**: Naming proof strategies aids transfer. A learner who has seen this pattern six times without a name will not recognize it as a general technique when they encounter `Finset.sum_insert` or `Finset.prod_insert` in W13-W14. A single sentence in a conclusion — e.g., "The insert step in finset induction almost always follows a 'decompose-compute-reassemble' pattern: rewrite the operation on `insert a s` using a decomposition lemma, simplify using `ha` and `ih`, then close the arithmetic" — would make this implicit knowledge explicit.

**Where**: Best placed in L04 or L05 conclusion (after the learner has seen it twice and can recognize the pattern).

**Effort**: Low (a sentence in a conclusion).

**Recommend**: Yes.

---

### 4. No level isolates the `absurd` + negation pattern that the base case sometimes requires

**What**: L04 uses `exact absurd h Finset.not_nonempty_empty` in the base case, and the stale L05_CardinalityByInduction uses `exact absurd h (Finset.insert_ne_empty a s')` in the insert case. The `absurd` tactic is introduced without a standalone exercise. The learner is told to use it but never has to figure out when and why `absurd` is the right move.

**Why**: `absurd` is a proof move that recurs whenever the induction base case has a vacuously false hypothesis. This pattern appears again in W13 (`sum_empty` when the hypothesis is about nonempty finsets) and W14 (range induction with impossible base cases). Teaching it explicitly here — perhaps as a remark about "when the base case hypothesis is impossible" — would improve transfer.

**Where**: A brief "why `absurd`?" remark in L04's introduction, or a dedicated sub-exercise before L04 where the learner must identify when a hypothesis contradicts the base case.

**Effort**: Low-medium (expanding L04's introduction or adding a small exercise).

**Recommend**: Consider.

---

### 5. L02's example is pedagogically weak — `s = ∅ ∨ s.Nonempty` does not require the inductive hypothesis

**What**: L02 proves `s = ∅ ∨ s.Nonempty`, which does not use `ih` at all. The conclusion correctly notes this ("we did not even need `ih`"). But as the first Finset induction proof, this sets a misleading precedent about what finset induction looks like. The learner might think finset induction is always this easy.

**Why**: The learner's first experience with a new proof technique shapes their mental model. A first example that uses `ih` — even a simple one like "every finset is finite" (trivial but pedagogically useful) or "if P holds for ∅ and is preserved by insert, then P holds for all s" — would give a more complete picture.

**Where**: L02 (modify the statement or swap in a different first example).

**Effort**: Medium (modifying a level).

**Recommend**: Consider.

---

### 6. L07 proves `card (range n) = n` but L09 (boss) proves `card (s ∪ t) ≤ card s + card t` — these are not thematically connected

**What**: L07 is a Nat induction level (proving `card (range n) = n`). The boss is a Finset induction level (proving subadditivity of union). There is no intermediate level that connects `range` to union or shows when one induction principle feeds into the other. The comparison is stated as a "rule of thumb" table but never exercised in a proof where the learner must actively choose.

**Why**: The plan says L07 should be "the same theorem proved both ways" — explicitly comparing Nat and Finset induction on the same statement. The implementation proves a statement that can only be done by Nat induction (since `range n` is parametrized by `n`). A true comparison level would present a theorem that admits both proofs and ask the learner to do one, with a remark about how the other works.

**Where**: L07 (modify the statement to one that admits both proof styles, e.g., "every finset contained in `range n` has card ≤ n").

**Effort**: High (restructuring a level).

**Recommend**: Consider.

---

### 7. The world does not foreshadow `Finset.sum` induction (W13-W14)

**What**: Finset induction is the backbone of big-operator proofs in W13 and W14. The conclusion of the boss (L09) mentions "what comes next" is the pset world (W10_ps) but says nothing about how the induction principle taught here underpins `sum_insert`, `sum_cons`, and inductive sum proofs.

**Why**: This is the most natural foreshadowing opportunity in the course. A sentence in L09's conclusion like "The `Finset.induction_on` principle you learned here is exactly how the big-operator library proves `sum_insert` and decomposes sums over finsets. When you reach the big-operator worlds, you will see this pattern again" costs nothing and creates a forward link.

**Where**: L09 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Yes.

---

### 8. The stale file `L05_CardinalityByInduction.lean` should be removed or integrated

**What**: There is a file `L05_CardinalityByInduction.lean` that is not imported by the world file. It contains a proof that `s = ∅ → s.card = 0` by finset induction. This content partially overlaps with L03 (which proves the converse).

**Why**: A stale file in the directory is confusing for maintenance and could accidentally be imported. If its content is valuable (and it is — the "both directions of an iff" pattern is good), it should be integrated into the world. If it duplicates existing content, it should be deleted.

**Where**: Either integrate into the world (e.g., as a level between L03 and L04 that completes the iff) or delete.

**Effort**: Low (delete) to medium (integrate).

**Recommend**: Yes.

---

### 9. `simp` is not in the DisabledTactic list for some levels, creating inconsistency

**What**: L01-L06, L08, L09 disable `trivial decide native_decide aesop simp_all` but do not disable `simp`. L07 adds `simp` to the disabled list. This inconsistency means `simp` can solve or partially solve goals in L01-L06 and L08-L09.

**Why**: The standard disabled set from the project memory is `trivial decide native_decide simp aesop simp_all`. Omitting `simp` from most levels is an oversight that could let learners bypass intended proof steps. For example, `simp` with appropriate lemmas could close the base cases in several levels without the learner understanding the decomposition.

**Where**: All levels except L07 (which already has `simp` disabled).

**Effort**: Low (add `simp` to DisabledTactic lines).

**Recommend**: Yes.

---

### 10. No concrete counterexample shows what goes wrong when `a ∈ s` in the insert step

**What**: L04 explains why `ha : a ∉ s` matters (it lets you rewrite `card (insert a s)` as `card s + 1`). But the world never shows a concrete case where `a ∈ s` and `insert a s = s`, so `card (insert a s) = card s` (no change). A quick example — e.g., `insert 2 {1, 2, 3} = {1, 2, 3}` — would make the lesson visceral.

**Why**: The "what if?" pattern is pedagogically powerful. The learner is told that `ha` matters, but never experiences the failure mode. A single concrete example in L04's introduction or conclusion would ground the abstract explanation.

**Where**: L04 introduction or conclusion (a worked example, not a new level).

**Effort**: Low (a few sentences).

**Recommend**: Consider.

---

## Overall impression

The world has a solid architectural skeleton: it opens with Nat induction review, introduces Finset induction, builds up through multiple exercises, provides a comparison level and a refine-style level, and closes with a genuine integration boss. The introductions and conclusions are well-written, with good "in plain language" transfer moments and clean comparison tables. The boss is appropriately challenging and uses the right inventory.

**The single most important improvement** is addressing the gap between L04 and L09: there is no level where the learner performs a complete finset induction proof with a cardinality goal that meaningfully uses `ih`. The current L05 (`CardInsertLe`) is a `by_cases` proof and L06 is a one-step `exact` application. The learner goes from "here is how the insert step works" (L04) to "prove subadditivity of union" (L09) without ever practicing the full induction-with-cardinality pattern on a simpler problem. Adding or restructuring L05-L06 to include a genuine induction-with-cardinality level is the highest-impact change. The stale `L05_CardinalityByInduction.lean` file suggests this content was intended but dropped — it should be reinstated or replaced with something better.
