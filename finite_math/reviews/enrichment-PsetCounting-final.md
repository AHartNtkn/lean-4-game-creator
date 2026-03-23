# Enrichment Review: PsetCounting

## Ranked Suggestions

### 1. Missing: Strict Inequality Level

**What**: No level exercises the strict inequality techniques from CountingTechniques L06-L07 (`card_lt_card`, `ssubset_iff_of_subset`, or the injection + non-surjectivity → `m < n` argument using `Finite.surjective_of_injective` and `subst`).

**Why**: CountingTechniques dedicated two full levels to strict inequality — one via strict subsets and one via functions. These are distinct proof moves from the `≤` bounds used everywhere in PsetCounting. The `subst` tactic was introduced in CT L07 and is never exercised in this pset. A problem set that tests four counting techniques but omits the strict inequality variant of one of them has a genuine retrieval gap.

**Where**: New level, between L03 (ComposedBounds) and L04 (LeagueDivisions), or between L06 and L07.

**Effort**: High (new level)

**Recommend**: Yes — this is the most significant technique gap. CT taught `card_lt_card`, `lt_of_le_of_ne`, `subst`, and `Finite.surjective_of_injective`. None of these appear in the pset. A level like "Given `f : Fin m → Fin n` injective and `b : Fin n` not in the range of `f`, prove `m < n`" would exercise all four tools.

---

### 2. Missing: Sandwich Equality via le_antisymm

**What**: L01 tests bijective counting using `card_congr` with an `Equiv`, but the alternative derivation via `le_antisymm` (CT L04) and the mutual injection principle (CT L18) are never exercised.

**Why**: CT L04 explicitly made the pedagogical point that bijective counting is a *theorem derivable from* injection + surjection bounds, not a separate axiom. CT L18 exercised this again with mutual injections. L01 uses the `card_congr` shortcut, which is the *other* approach. The `le_antisymm` derivation — arguably the deeper insight — gets zero retrieval practice.

**Where**: New level or modification of L01. A problem like "Given `f : α → β` injective and `g : β → α` injective, prove `Fintype.card α = Fintype.card β`" would directly exercise `le_antisymm` + dual injection bounds without overlap with L01's Equiv approach.

**Effort**: High (new level) or Medium (replace L01)

**Recommend**: Yes — the `le_antisymm` strategy is a cornerstone technique. Testing only the `card_congr` shortcut leaves the derivation unexercised.

---

### 3. L06 (Indirect Bound) Lacks Concrete Motivation

**What**: L06 presents the composition argument (`f` surjective, `g ∘ f` injective → `card β ≤ card γ`) in fully abstract terms with no scenario or explanation of when this pattern arises.

**Why**: L04 motivates double counting with "sports league divisions." L05 motivates generalized pigeonhole with "items in categories." L07 motivates chaining with "two functions, two steps." L06 just says "two functions, one has a property, the other composition has a property" — entirely structural. A concrete scenario would make the composition reasoning feel purposeful rather than algebraic. For example: "A company assigns employees to teams (surjectively), and a performance system ranks team outputs (injectively when composed with the assignment). What can you conclude about the number of teams vs. the number of rankings?"

**Where**: L06 introduction text.

**Effort**: Low (rewrite introduction paragraph)

**Recommend**: Yes — every other multi-technique level has a motivating scenario; L06 is the exception.

---

### 4. The hmem Boilerplate Pattern Deserves Explicit Naming

**What**: The membership proof `fun _ _ => Finset.mem_univ _` appears in L04, L05, and L08. L04's conclusion mentions it in passing ("you'll need it again in the boss"), but it's never named as a reusable proof idiom.

**Why**: This boilerplate is the single most repeated proof fragment in the double-counting workflow. Students who struggle with it are likely tripped up by the lambda syntax, not the mathematical content. Explicitly naming it (e.g., "the universal membership lemma" or "the univ-maps-to-univ step") and explaining the lambda structure once would reduce cognitive overhead on subsequent uses.

**Where**: L04 introduction or conclusion — first place it appears.

**Effort**: Low (add a paragraph to L04's conclusion or introduction)

**Recommend**: Consider — the pattern is acknowledged but not named. Naming it would help students recognize it as a repeatable move.

---

### 5. No Level Exercises Finset-Level Counting (as opposed to Fintype-Level)

**What**: Every level in PsetCounting operates on `Fintype.card` and `Finset.univ`. No level uses Finset-level cardinality arguments such as `Finset.card_le_card` (from subset inclusion) or Finset-level filter/image bounds.

**Why**: CountingTechniques L06 explicitly taught `Finset.card_lt_card` and `Finset.ssubset_iff_of_subset` — tools that operate on named Finsets rather than `Finset.univ`. The boss conclusion mentions that "Fintype-level counting theorems have Finset-level counterparts" and that the Finale will combine both levels. A pset level that works with specific named Finsets (not just `univ`) would bridge this gap and foreshadow the Finale.

**Where**: New level.

**Effort**: High (new level)

**Recommend**: Consider — this connects to suggestion #1 (strict inequality via `card_lt_card` operates at the Finset level). Combining both into one level would address two gaps simultaneously.

---

### 6. Boss Conclusion Could Articulate the "Information Chaining" Meta-Strategy More Explicitly

**What**: The boss combines injection bound + fiber decomposition + sum bounding + contradiction. L07's conclusion names this "information chaining." The boss conclusion mentions the proof chain but doesn't connect back to L07's naming or articulate it as a general strategy.

**Why**: The boss is the capstone. Its conclusion should synthesize the world's meta-lessons, not just describe the proof steps. The key insight — "use one function's property to constrain a type's size, then feed that constraint into a different technique on another function" — is the pattern students should carry forward. The conclusion describes *what* happened but not *why* the strategy works in general.

**Where**: L08 conclusion.

**Effort**: Low (add a paragraph)

**Recommend**: Consider — the conclusion is already long and includes a good three-strategy comparison for negation. But the chaining meta-strategy deserves equal emphasis.

---

### 7. No Counterexample or Misconception Level

**What**: No level addresses a common false generalization about counting techniques. For example: "If `card α < card β`, does that mean there exists a surjection `α → β`?" (No — surjectivity requires `card α ≥ card β`, not `<`.) Or: "If `f` is not injective, does `card α > card β`?" (No — `f` can be non-injective even when `card α ≤ card β`.)

**Why**: CountingTechniques L06's conclusion explicitly warns that "the converse is false: `s.card < t.card` does NOT imply `s ⊂ t`." This kind of reasoning — understanding where a technique does NOT apply — is valuable for a problem set that tests technique selection.

**Where**: New level.

**Effort**: High (new level)

**Recommend**: Consider — misconception levels are high-value but this pset already has 8 levels. If the strict inequality level (suggestion #1) is added, a misconception level might make the world too long.

---

### 8. L03 Conclusion's Duality Table Could Be Exercised

**What**: L03's conclusion presents a clean duality table (injective ↔ `card source ≤ card target`, surjective ↔ `card target ≤ card source`). No subsequent level asks the student to USE this duality — for example, a level where the student must choose between the injection bound and the surjection bound based on which direction the inequality needs to go.

**Why**: L06 requires the student to combine injection and surjection bounds, but the choice is forced by the hypothesis structure (the composition is injective, f is surjective). A level where BOTH bounds are available and the student must select the right one based on the goal direction would test the duality understanding more directly.

**Where**: New level or modification of an existing level.

**Effort**: Medium (new level with constrained design)

**Recommend**: Consider — L06 partially tests this but the technique selection is constrained by the hypotheses. A level with more freedom would better test the duality table.

---

## Overall Impression

PsetCounting is a well-structured problem set that progresses cleanly from single-technique retrieval (L01-L05) to multi-technique integration (L06-L08). The technique variety is good: bijective counting, pigeonhole, double counting, and information chaining all appear. The boss genuinely requires multi-step reasoning.

**The single most important improvement** is adding a strict inequality level (suggestion #1). CountingTechniques spent two levels on strict bounds (`card_lt_card`, `lt_of_le_of_ne`, `subst`, `Finite.surjective_of_injective`) and the pset exercises none of them. This is not a minor omission — it's an entire proof-move cluster with a dedicated tactic (`subst`) that gets zero retrieval practice. Adding one level that requires strict inequality reasoning would close the largest technique gap in the world.
