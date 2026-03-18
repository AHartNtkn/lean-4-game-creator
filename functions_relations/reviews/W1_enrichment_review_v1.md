# W1: SetsAndMembership — Enrichment Review v1

**Reviewer**: enrichment-reviewer
**Date**: 2026-03-18
**World**: W1 SetsAndMembership (11 levels: L01–L11)
**Verdict**: FAIL — 3 high-impact opportunities, 4 medium-impact opportunities

---

## Ranked Suggestions

### 1. Missing practice level for `.mp` / `.mpr` before they are required in L10

**What**: L07 (IfAndOnlyIf) introduces the iff concept and mentions `.mp` / `.mpr` in the conclusion, but the learner never practices using them. L10 (DoubleInclusion) then requires `(h x).mp hx` and `(h x).mpr hx` — two new micro-skills (dot projection on iff + function application to a universal + passing the result) used together with no prior hands-on experience.

**Why**: This violates the one-new-thing-per-level principle. L10 combines (a) first use of `.mp`/`.mpr`, (b) first use of a universal iff hypothesis `h : ∀ x, P x ↔ Q x` requiring `(h x)` before `.mp`, and (c) the double-inclusion proof shape. A learner who has only seen `.mp`/`.mpr` in a conclusion blurb will not know how to write `(h x).mp hx`. This is exactly the kind of implicit skill that reference 07 warns about: "If the proof requires the learner to provide explicit arguments... but this skill is never isolated, it will feel like a trick when needed."

**Where**: Insert a new level between L07 and L08 that isolates `.mp` / `.mpr` usage. For example: given `h : P ↔ Q` and `hp : P`, prove `Q` using `exact h.mp hp`. Then a second goal or a follow-up: given `h : ∀ x, P x ↔ Q x` and `hp : P 5`, prove `Q 5` using `exact (h 5).mp hp`. This builds the `(h x).mp` idiom before L10 needs it.

**Effort**: High (new level)

**Recommend**: Yes

---

### 2. `omega` used without formal introduction

**What**: L01 and L02 both close goals using `omega`, but `omega` has no `NewTactic`, no `TacticDoc`, and no introduction in any intro text. The learner is told "Use `omega` to close arithmetic goals involving natural numbers" but the tactic simply appears without being formally added to inventory.

**Why**: The hints tell the learner what to type, so they can mechanically complete the level. But `omega` then never appears again in the world, so the learner has no understanding of what `omega` does, when it applies, or whether it will be available later. For a course that carefully introduces every other tactic with a `TacticDoc` and `NewTactic`, this is an inconsistency. Either formalize `omega` with a doc entry, or replace the arithmetic closure with something that doesn't require an undocumented tactic (e.g., use `Nat.lt_of_lt_of_le` or restructure L01/L02 so the arithmetic step is handled differently).

**Where**: L01 (add `NewTactic omega` and `TacticDoc omega`)

**Effort**: Low (add two DSL entries + a sentence in the intro)

**Recommend**: Yes

---

### 3. L06 introduces `Set.univ` but never proves anything about it

**What**: L06 is titled "The Empty Set and the Universal Set" and introduces both `∅` and `Set.univ` as `NewDefinition`. But the statement is only `∅ ⊆ A`. The learner reads about `Set.univ` and its properties (`x ∈ Set.univ` is `True`, `A ⊆ Set.univ` for any `A`) but never proves any of these facts. The definition is introduced but has zero practice.

**Why**: Coverage state for `Set.univ` is stuck at I (introduced) with no S (supported practice). The learner's only contact with `Set.univ` is reading about it. The reference on coverage states (05) says "If an item never progresses beyond I, coverage is weak." Proving `A ⊆ Set.univ` would be a short, satisfying level that also teaches the `trivial` alternative pattern (the goal reduces to `True` after `intro x hx`, and the learner uses `trivial` — except `trivial` is disabled, so they need another approach like `exact Set.mem_univ x` or `change True; exact trivial`... actually, since `trivial` is disabled, the learner would need to handle `True` directly). This also raises a design question: how does the learner close a `True` goal when `trivial` is disabled? This is worth resolving explicitly.

**Where**: Split L06 into two levels: L06a proves `∅ ⊆ A`, L06b proves `A ⊆ Set.univ`. The second level needs a way to close a `True` goal — either re-enable `trivial` for that one level, teach `exact trivial` as a special case, or use `show True` + `exact ⟨⟩` (since `True` has a single constructor). This is also a natural place to introduce `exact ⟨⟩` or `constructor` as the way to prove `True` — a micro-skill that will generalize.

**Effort**: High (new level + design decision about closing `True`)

**Recommend**: Yes

---

### 4. ⊆ / ⊂ confusion misconception is missing

**What**: The plan's misconception map (line 89) says "⊆ and ⊂ confusion" should be addressed in W1 with a "docstring warning." No mention of `⊂` (strict/proper subset) appears anywhere in the 11 level files.

**Why**: This is a misconception the plan explicitly identified as needing attention in W1. Learners coming from standard math notation may not realize that `⊆` in Lean means "subset or equal" (i.e., it allows equality), and `⊂` (which exists as `HasSSubset.SSubset` in Lean) means strict subset. A one-sentence warning in L03's intro or conclusion — "Note: `⊆` allows equality. Lean also has `⊂` (strict subset, meaning `A ⊆ B ∧ A ≠ B`), but we will not use it in this course." — costs nothing and prevents confusion.

**Where**: L03 (SubsetProofs) intro or the DefinitionDoc for `⊆`

**Effort**: Low (one sentence in a docstring or intro)

**Recommend**: Yes

---

### 5. No level isolates the `intro x hx` subset pattern on a non-reflexive, non-trivial concrete set

**What**: L03 proves `A ⊆ A` (reflexivity — trivially closing with `exact hx`). L04 uses a given hypothesis `h : A ⊆ B`. L05 chains two subset hypotheses. But no level asks the learner to prove a concrete subset relationship like `{x : ℕ | x > 5} ⊆ {x : ℕ | x > 3}` where the chase step requires actual work (here, arithmetic). This is the natural companion to L01/L02 — those levels proved concrete membership; a concrete subset level would combine the subset pattern from L03 with the change/show + omega pattern from L01/L02.

**Why**: Without this, the subset proof pattern's "prove it belongs to the right-hand set" step (step 3 from L03's recipe) is always trivial or delegated to hypothesis application. The learner never experiences the chase step requiring real reasoning inside a subset proof until much later. A concrete subset level would bridge L02 and L03's abstract patterns, providing a grounding example (coverage axis: EXAMPLE).

**Where**: New level between L03 and L04 (or between L02 and L03). Statement: `{x : ℕ | x > 5} ⊆ {x : ℕ | x > 3}`. After `intro x hx`, the learner does `change x > 5 at hx; change x > 3; omega`.

**Effort**: High (new level)

**Recommend**: Consider

---

### 6. Conclusion of L08 (first ext level) could name the "ext → constructor → chase" pattern more forcefully for transfer

**What**: L08's conclusion names the pattern and gives a recipe, but does not provide the plain-language mathematical translation that L11's boss conclusion does so effectively ("To show A = B, we show they have the same elements. Take any x..."). The first time the learner encounters this pattern deserves the same dual presentation — Lean recipe AND mathematical prose — so the transfer layer is activated from the start.

**Why**: The boss conclusion (L11) has an excellent mathematical translation of the proof. But the learner encounters the pattern three levels earlier in L08. If the mathematical prose appears only at L11, the learner has done three ext proofs (L08, L09, L11) before seeing the English version. Moving the prose (or a shorter version) to L08's conclusion activates the transfer layer earlier, which aligns with reference 00's guidance: "Good conclusions... translate the Lean proof into ordinary mathematical language."

**Where**: L08 conclusion — add 2-3 sentences of mathematical prose alongside the Lean recipe.

**Effort**: Low (add sentences to existing conclusion)

**Recommend**: Yes

---

### 7. The boss (L11) is structurally identical to what `Set.Subset.antisymm` + `ext` already demonstrated in L10

**What**: L10 proves set equality using `Set.Subset.antisymm` with a pointwise iff hypothesis. L11's boss proves the same theorem shape (A = B from A ⊆ B and B ⊆ A) using `ext` instead of `Set.Subset.antisymm`. The "integration" is really just: do L10 but start with `ext` instead of `apply Set.Subset.antisymm`. Both directions of the boss are single-step (`exact h1 hx`, `exact h2 hx`), so the chase step is trivial.

**Why**: Reference 00 says "A boss is bad when it is... just longer than the earlier levels... or solved by replaying one example." This boss is essentially a combination of L08's ext pattern with L04's subset-hypothesis application. Each direction requires only one tactic after `intro hx`. The proof is 5 lines: `ext x; constructor; intro hx; exact h1 hx; intro hx; exact h2 hx`. A stronger boss would require the learner to do actual membership chasing in at least one direction — for example, proving `{x : ℕ | P x ∧ Q x} = {x : ℕ | Q x ∧ P x}` from scratch using ext, with conjunction manipulation in the chase (combining L09's conjunction work with the ext pattern), AND subset hypotheses in the mix. Alternatively, the boss could combine double inclusion with a non-trivial chase, e.g., given `A ⊆ B`, `B ⊆ C`, `C ⊆ A`, prove `A = B` (requires transitivity + antisymmetry).

**Where**: L11 — redesign the boss statement to require deeper integration.

**Effort**: Medium (modify existing level)

**Recommend**: Consider

---

## Overall Impression

**What works well**: The world has a clear, logical progression. L01–L02 (membership via show/change) → L03–L05 (subsets) → L06 (special sets) → L07 (iff) → L08–L09 (extensionality) → L10 (double inclusion) → L11 (boss). The intro and conclusion text is consistently high quality, with clear recipes and good scaffold fade. The hints are properly layered (strategy first, code second). The `ext → constructor → chase` pattern is well-named and well-reinforced.

**Single most important improvement**: Insert a level between L07 and L08 that isolates `.mp` / `.mpr` usage on an iff hypothesis before L10 requires it in the `(h x).mp hx` form. This is the world's most significant coverage gap — a micro-skill that is documented but never practiced before it is required. Without it, L10 asks the learner to combine three new elements (dot projection, universal instantiation, and the double-inclusion proof shape) in a single level.
