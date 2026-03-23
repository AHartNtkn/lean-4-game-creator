# Plan Review: functions_relations

**Date**: 2026-03-23
**Plan reviewed**: `functions_relations/PLAN.md`
**Coverage map**: `functions_relations/coverage-map.md`
**Course description (long_term.md)**: Course 2 — "Sets, functions, relations, equivalences, subtypes, and countability"

---

## 1. Scope Completeness

The plan covers all major topics specified in `long_term.md`:

- Sets as predicates: W01-W05
- Images/preimages: W06-W08
- Restriction to subsets (InjOn, SurjOn, BijOn, MapsTo): W13-W14
- Injective/surjective/bijective maps: W09-W12
- Relations as sets of pairs: W15 (partially — see P1 defect below)
- Bundled equivalences: W22
- Partial equivalences: W23
- Subtypes and `↥s`: W21
- Countable sets and Encodable types: W25-W27
- Equality vs equivalence vs isomorphism distinction: W20

The course description says this is "the language course for modern mathlib" and the plan treats it that way — it's not a shallow survey. 28 worlds across 8 phases is substantial and covers the full scope described.

**Verdict: No scope gaps.**

---

## 2. Coverage Map Alignment

### Core items from Section 2 of coverage map

All 19 core items listed under "Core items that must not be missed" have corresponding worlds:

| Core item | Plan coverage |
|-----------|--------------|
| Set as predicate | W01 |
| Subset as universal implication | W02 |
| Set extensionality | W02 |
| Set operations reduce to logic | W03 |
| Image/preimage + asymmetry | W06-W08 |
| Injective/Surjective/Bijective | W09-W12 |
| On-set variants | W13-W14 |
| Composition laws | W09-W12 |
| Left/right inverse | W09-W11 |
| Relation as predicate or subset of product | W15 (predicate only — see P1 #1) |
| Equivalence relation | W15 |
| Setoid and Quotient | W16-W17 |
| Well-definedness obligation | W17 |
| Partition ↔ equivalence | W19 |
| Subtype | W21 |
| Equiv | W22 |
| Countable/Encodable/Denumerable | W25 |
| Cantor's theorem | W26 |
| Countability closure | W25 |

### Closure risks

The coverage map's "Needs architect judgment" items are all resolved:
- On-set function properties: dedicated world W13 + pset W14. Correct decision.
- Cantor placement: in countability section (W26). Good — makes it the capstone of the countability story.
- ℤ-from-ℕ×ℕ: W18 boss. Good placement as a major integration exercise.
- Indexed unions/intersections: separate world W04. Good — the binder notation is genuinely new.
- Encodable depth: core but practical. Reasonable.
- Subtype vs Set balance: dedicated world W21. Correct.

### Example plan

The coverage map's example plan is well-represented in level sketches. Nearly every example from Section 3 of the coverage map appears somewhere in the plan. The key examples — `fun n => 2*n` (injective, not surjective), mod-3 equivalence, ℤ-from-ℕ×ℕ quotient, `Fin 2 ≃ Bool`, Cantor diagonalization — are all present and placed at appropriate points.

**One gap**: The coverage map lists `fun (a, b) : ℕ × ℕ => a + b` as a counterexample for non-injectivity with "kernel has nontrivial equivalence classes." This specific example doesn't appear in the plan but the concept is covered through `Setoid.ker f` in W16. Not critical.

---

## 3. World Graph Coherence

### Center of gravity

Most worlds have a clear single center:
- W01: sets as predicates
- W02: subsets and set equality
- W03: set operations ↔ logic
- W06: preimages
- W07: images
- W09: injectivity
- W10: surjectivity
- W15: relations and equivalence properties
- W16: setoids and quotients
- W17: quotient lifting
- W19: partitions
- W22: Equiv
- W26: Cantor and diagonalization

**W04 is the weakest center**: it bundles indexed unions/intersections (its stated center) with cartesian products, Nonempty, and powerset. These are four distinct concepts. The indexed operations (iUnion, iInter, bounded variants) form a coherent family, but `Set.prod`, `Set.Nonempty`, and `Set.powerset` are tangentially related at best. See P2 #1.

### Dependency ordering

The dependency graph is sound. No world depends on material taught later, with one exception:

**W17 L06 uses `≃` notation** (via `Setoid.quotientKerEquivRange`) before `Equiv` is formally taught in W22. The plan places the first isomorphism theorem result in W17 (Phase 5), but Equiv understanding is Phase 6. See P1 #3.

### World type mix

- 19 lecture worlds
- 7 pset worlds
- 1 example/review world (W20)
- 1 capstone (W28)

This is a good mix. Every lecture phase has a corresponding pset. W20 provides a conceptual consolidation point. W28 integrates everything.

Pset pairing:
- W01-W04 → W05 (PsetSets) ✓
- W06-W07 → W08 (PsetImgPreimg) ✓
- W09-W11 → W12 (PsetFunctions) ✓
- W13 → W14 (PsetRestricted) ✓
- W15-W17 → W18 (PsetRelations) ✓
- W21-W23 → W24 (PsetTypesEquiv) ✓
- W25-W26 → W27 (PsetCountability) ✓

---

## 4. Proof-Move Coverage

The plan has an explicit proof-move coverage table (Section 5) mapping every core proof move through all five stages (I, S, R, G, T). This is one of the plan's strongest features.

All core proof moves have complete 5-stage coverage:

| Move | I | S | R | G | T |
|------|---|---|---|---|---|
| Unfold membership | W01 | W01-W04 | W05 | all bosses | W05, W08 |
| Subset by `intro x hx` | W02 | W02, W03 | W05 | W03 boss | W05, W14 |
| Set equality by `ext` | W02 | W02, W03 | W05 | W03 boss | W05, W08 |
| Image witness | W07 | W07 | W08 | W07 boss | W08, W28 |
| Injectivity proof | W09 | W09 | W12 | W09 boss | W12, W13 |
| Surjectivity proof | W10 | W10 | W12 | W10 boss | W12, W13 |
| Diagonal argument | W26 | W26 | W27 | W26 boss | W27, W28 |
| Quotient lift | W17 | W17 | W18 | W17 boss | W18 |
| Partition ↔ equivalence | W19 | W19 | W28 | W19 boss | W28 |

Bosses integrate multiple proof moves as required:
- W03 boss: ext + ↔ + case analysis on ∨ + combining ∧/∨
- W07 boss: image witness + preimage unfold + surjectivity
- W17 boss: lift + well-definedness + inductionOn
- W28 boss: partition ↔ equivalence round-trip (all themes)

**Verdict: Strong. The proof-move map is explicit and complete.**

---

## 5. Granularity Plan

### Novelty budgets

Most worlds respect the "one new burden per level" constraint. Level sketches clearly identify the dominant lesson for each level.

**Potential overloads**:
- W04 introduces 6 new definitions across 8 levels (iUnion, iInter, bounded variants, cartesian product, Nonempty, powerset). Per-level novelty is 1, but the cumulative burden within one world is high, especially since 3 of these (cartesian product, Nonempty, powerset) aren't "indexed operations." See P2 #1.
- W13 introduces 5 new definitions across 7 levels (MapsTo, InjOn, SurjOn, BijOn, EqOn). Per-level novelty is 1. The center of gravity ("on-set function properties") is coherent, so this is acceptable.
- W25 introduces 4 new concepts across 9 levels (Countable, Encodable, Denumerable, Set.Countable + closure). This is reasonable given the 9 levels.

### Boss integration

The boss map (Section 7) is excellent. Each boss clearly lists its integrated subskills and source levels. Every boss integrates 2+ proof moves from its world. No boss depends on untaught micro-skills (checked against level sketches and inventory release).

---

## 6. Coverage Closure

### Core items with strong closure (all 5 stages present)

The majority of core items have strong closure. I verified each row of the coverage closure table (Section 5 of PLAN.md). Items with complete I → S → R → G → T chains:

- `Set α`, `∈`, `⊆`, `setOf`, `∪`/`∩`, `ᶜ`/`\`, `Set.image`, `Set.preimage`
- `Function.Injective`, `Function.Surjective`, `Function.Bijective`
- `Function.LeftInverse`, `Function.RightInverse`
- All on-set function properties (MapsTo, InjOn, SurjOn, BijOn)
- Equivalence, Setoid, Quotient, Quotient.lift
- Partition ↔ equivalence correspondence
- `Subtype`, `Equiv`, Cantor's theorem
- All core proof moves

### Items with partial or weak closure

| Item | Stages present | Missing | Severity |
|------|---------------|---------|----------|
| `Denumerable` | I(W25), S(W25) | R, G, T | **Weak** — core item with only 2/5 stages |
| `Encodable` | I(W25), S(W25), R(W27), G(W25 boss) | T | Partial — core item missing transfer |
| `Set.Nonempty` | I(W04), S(W04, W07), R(W05) | G (marked "—") | Partial — core item missing boss integration |
| Binary relation as `Set (α × α)` | Conceptual mention in W15 | I, S, R, G, T (all practical) | **Illusory** — see P1 #1 |
| `Set.sUnion`/`Set.sInter` | Not in any level sketch | All | Absent from levels (supporting, so acceptable) |
| `Set.diagonal` | Conceptual in W15 | All practical | Supporting item; acceptable |

**`Denumerable` is the most concerning**: it's marked core in the coverage map but has only introduction + supported practice. It never appears in a pset, boss, or transfer context.

---

## 7. Transfer Plan

Section 8 of the plan provides an explicit transfer and retrieval table for 9 high-value moves. Each has a clear chain: first appearance → supported practice → reduced support → fresh surface form → plain-language transfer statement.

The transfer plan is real and specific:
- Pset worlds provide fresh surface forms (ℤ instead of ℕ, abstract sets instead of concrete, different functions)
- The finale (W28) provides integration-level transfer across all themes
- W20 (ThreeSamenessWorld) provides the key conceptual transfer for =, ≈, ≃

**Verdict: Transfer plan is present and substantive.**

---

## 8. Inventory Release Plan

Section 6 provides detailed tables for:
- Tactic release schedule with rationale
- Baseline disabled tactics
- Per-world additional disabling with reasons
- Definition/theorem release schedule with world, rationale, and tab

The gating strategy is well-designed:
- `tauto` disabled in set-logic and relation-checking worlds
- `omega` disabled on concrete ℕ levels
- `ext` hidden in W02 L01-L04, then taught
- Composition lemmas (Injective.comp, etc.) disabled in function worlds
- `Quotient.eq` disabled in quotient worlds
- Lattice alias exploit vector documented and addressed with DisabledTheorem plan
- One-line closer Set lemmas addressed

**One concern**: `rintro` and `rcases` are marked "Hidden until W07" but never explicitly taught. They're marked "needed, not explicitly taught." Given that `rintro`/`rcases` are in the coverage map's LEAN axis as core items (I S R G), they should either get explicit teaching or the decision to leave them as discovery items should be documented with rationale.

**Verdict: Strong. The inventory release plan is thorough and addresses the major exploit vectors.**

---

## 9. Example and Counterexample Plan

### Definitions with concrete examples

Every major definition has at least one planned concrete example:

| Definition | Example(s) in level sketches |
|-----------|------------------------------|
| `Set α` | `{n : ℕ \| n < 5}`, `{n : ℕ \| Even n}` |
| `⊆` | `{n \| n < 3} ⊆ {n \| n < 5}` |
| `∪`, `∩`, `ᶜ`, `\` | Multiple concrete instances |
| `f '' s` | `(fun n => 2*n) '' {0,1,2,3}` |
| `f ⁻¹' t` | `(fun n => n%2) ⁻¹' {0}` |
| `Injective` | `fun n => n + 1`, `fun n => 2*n` |
| `Surjective` | `fun n : ℤ => n + 1`, `fun n => n/2` |
| Equivalence relation | mod 3, same parity |
| `Setoid`/`Quotient` | ℤ mod 3, kernel of mod-3 projection |
| Partition | ℤ into even/odd, mod-3 residue classes |
| `Subtype` | `{n : ℕ // n > 0}` |
| `Equiv` | `Fin 2 ≃ Bool`, `{n // n > 0} ≃ ℕ` |
| `PartialEquiv` | ℕ ↔ ℕ with source `{n \| n > 0}` |
| `Countable` | ℕ, ℤ, ℚ, ℕ × ℕ |
| Uncountable | `Set ℕ`, `ℕ → Bool` |

### Counterexamples

| What it disproves | Example | Location |
|-------------------|---------|----------|
| Image preserves intersection | `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` (only ⊆) | W07 L04 |
| `Injective` of composition → `Injective` of `g` | Explicit discussion | W12 L03 |
| `InjOn f s` → `Injective f` | Concrete counterexample | W13 L03 |
| `≤` is an equivalence relation | Not symmetric: `0 ≤ 1` but `¬ 1 ≤ 0` | W15 L04 |
| Some relation is transitive | Counterexample | W15 L05 |
| Partition with overlapping parts | `{{1,2}, {2,3}, {4}}` | W19 L03 |
| Partition with empty part | `{{1,2}, ∅, {3}}` | W19 L04 |
| Function can always be lifted | Well-definedness failure | W17 L03 |

**Gap**: No explicit level for a non-reflexive relation (e.g., `≠` on ℕ). The coverage map lists this under both the EXAMPLE axis ("Not reflexive: `≠` on ℕ") and MISCONCEPTION axis. W15 has counterexamples for non-symmetry (L04) and non-transitivity (L05) but not non-reflexivity. See P1 #4.

---

## Defects

### P0 (blocking)

None.

### P1 (high)

1. **Binary relation as `Set (α × α)` — illusory coverage**. The coverage map marks "Binary relation as `Set (α × α)` or `α → α → Prop`" as core with "Two representations; must connect both." The plan only teaches the `α → α → Prop` representation. The `Set (α × α)` representation is mentioned "conceptually" in W15's description but no level requires the learner to work with it. The learner never sees `Set.diagonal`, never works with a relation as a subset of a product, and never translates between the two representations. This is a core item with illusory closure.

   **Fix**: Add 1-2 levels to W15 where the learner works with a relation as a `Set (α × α)`, uses `Set.diagonal` for the equality relation, and translates between the `α → α → Prop` and `Set (α × α)` representations.

2. **`Denumerable` has weak closure despite core status**. The coverage map marks `Denumerable` as core (I S R G). The plan introduces it in W25 L04 and practices it in W25 but it never appears in a boss (W25 boss uses `Countable`, not `Denumerable`), never appears in a pset (W27 doesn't reference it), and has no transfer. It's effectively introduced and then abandoned. If it's truly core, it needs retrieval and integration. If it's not core, the coverage map should be updated.

   **Fix**: Either (a) add a W27 level requiring `Denumerable.eqv` or an explicit `α ≃ ℕ` construction, and include `Denumerable` in the W25 boss; or (b) demote `Denumerable` to supporting in the coverage map.

3. **W17 L06 introduces `≃` notation before Equiv is taught**. `Setoid.quotientKerEquivRange` produces a result of type `Quotient (ker f) ≃ ↑(Set.range f)`. Equiv isn't formally taught until W22 (Phase 6), but W17 is in Phase 5. The learner encounters `≃` in a level that requires understanding what the result means. W20 L04 foreshadows `≃` conceptually, but W20 comes after W17 in the phase ordering. This creates either a hidden dependency (W17 should depend on W22) or a pedagogical mismatch.

   **Fix**: Either (a) move W17 L06's content to W28 L01 (which already covers the same theorem) and drop L06 from W17, reducing W17 to a 6-level world focused purely on lift/well-definedness/induction; or (b) change W17 L06 to a "preview" level where the result is shown but the learner's task doesn't require working with the `≃` structure itself.

4. **Missing non-reflexive counterexample**. The coverage map lists "Not reflexive: `≠` on ℕ — symmetric but not reflexive" as a planned counterexample. W15 has counterexamples for non-symmetry (L04: `≤`) and non-transitivity (L05) but no level for non-reflexivity. This means the learner checks reflexivity (L01), symmetry (L02), transitivity (L03), sees that `≤` fails symmetry (L04), and sees that something fails transitivity (L05), but never sees a relation that fails reflexivity. The three-property framework is incomplete without all three failure modes.

   **Fix**: Add a level to W15 (e.g., between L05 and L06) where the learner proves `¬ Reflexive (· ≠ · : ℕ → ℕ → Prop)`.

### P2 (medium)

1. **W04 has a diffuse center of gravity**. W04 is titled "IndexedOpsWorld" but includes cartesian products (`Set.prod`), `Set.Nonempty`, and `Set.powerset` alongside indexed unions/intersections. These are not "indexed operations" — they're distinct concepts with different proof shapes. This violates the "each world has one center of gravity" principle.

   **Fix**: Consider splitting W04 into two worlds: (a) IndexedOpsWorld for `iUnion`, `iInter`, bounded variants, and their proof shapes (existential/universal); (b) fold `Set.prod`, `Set.Nonempty`, and `Set.powerset` into W03 (SetOpsWorld) as additional levels, or into PsetSets (W05) where they can serve as fresh surface forms. This would add one world to the count (29 total) but improve coherence.

2. **`Set.Nonempty` is core but has no boss integration**. The coverage closure table shows G="—" for `Set.Nonempty`. It's introduced in W04, practiced in W04 and W07, retrieved in W05, but never appears as a subskill in any boss. Given that nonemptiness is a core item used throughout mathematics, it should appear in at least one boss.

   **Fix**: Include a `Set.Nonempty` obligation in the W07 boss (which already involves surjectivity conditions and image reasoning, where nonemptiness naturally arises).

3. **`Encodable` is core but has no transfer stage**. Coverage closure shows T="—" for `Encodable`. It's introduced and practiced in W25, retrieved in W27, and integrated in the W25 boss, but never appears in a fresh surface form. If `Encodable` is truly core (the long_term.md catalog says "encodable types" explicitly), it should have transfer.

   **Fix**: Add a W27 level that requires building an `Encodable` instance for a type the learner hasn't seen before (not ℕ, ℤ, or ℚ), such as `Option ℕ` or a small sum type.

4. **`rintro`/`rcases` are core LEAN-axis items but never explicitly taught**. They're marked "needed, not explicitly taught" and "Hidden until W07." The coverage map lists them as core. While discovery-based learning has merit, pattern-matching destructuring is a genuine new skill that many learners will struggle with if not shown explicitly.

   **Fix**: Add a brief introduction of `rintro` at the point where it's first needed (W07, alongside `obtain`), with a level that shows the pattern-matching syntax explicitly before the learner is expected to use it.

---

## Specific Recommendations (ranked)

1. **(P1)** Add 1-2 levels to W15 for binary relations as `Set (α × α)` and the `Set.diagonal` definition. This is needed for the core coverage item.

2. **(P1)** Resolve the W17 L06 / Equiv dependency: either drop L06 from W17 (move to W28) or make it a preview level that doesn't require Equiv proficiency.

3. **(P1)** Add a non-reflexive counterexample level to W15 (e.g., `¬ Reflexive (· ≠ ·)`).

4. **(P1)** Strengthen `Denumerable` closure: add it to the W25 boss or a W27 level, or demote it to supporting in the coverage map.

5. **(P2)** Split W04 to separate indexed operations from Set.prod/Nonempty/powerset, or document why the mixed center is acceptable.

6. **(P2)** Add `Set.Nonempty` to a boss (W07 boss is the natural candidate).

7. **(P2)** Add `Encodable` transfer to W27 with a fresh type.

8. **(P2)** Teach `rintro`/`rcases` explicitly at W07 rather than leaving them as hidden discovery items.

---

## Red Flag Check

| Red flag | Status |
|----------|--------|
| Boss depends on untaught micro-skill | **Clear** — all bosses use skills from their level ladders |
| World mixes unrelated theorem families | **W04 flagged** — but not severely enough to block |
| Missing docs for newly unlocked inventory | **Clear** — inventory release plan specifies all items |
| Hints don't match failure states | **N/A** — hints are per-world, not plan-level |
| Psets merely clone lecture examples | **Clear** — psets use fresh surface forms and different types |
| Level introduces too many new burdens | **Clear** — level sketches respect 1-burden rule |
| Major definition never exercised on concrete example | **Clear** — all major definitions have concrete examples |
| Unresolved local-run or publish breakage | **N/A** — plan stage, not code |

---

## Overall Verdict: **FAIL**

The plan is strong overall — the proof-move map is explicit and complete, the transfer plan is substantive, the inventory release is thorough, and the world graph is mostly sound. However, it fails on the coverage closure criterion:

- **One core item has illusory closure**: binary relations as `Set (α × α)` — mentioned conceptually but never practiced. The coverage map says "must connect both" representations.
- **One core item has weak closure**: `Denumerable` — introduced but never retrieved, integrated, or transferred.
- **A dependency issue** in W17 L06 that introduces `≃` before it's taught.
- **An incomplete counterexample set** in W15 (missing non-reflexive example).

These are all fixable with targeted changes (adding ~4-5 levels total across existing worlds). None requires restructuring the plan. The fixes are localized and the plan's architecture is sound.
