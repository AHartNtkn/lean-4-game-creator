# Plan Review: Functions & Relations

**Reviewer**: Plan review skill
**Date**: 2025-03-18
**Plan reviewed**: `lean4game-functions-relations/PLAN.md`
**Coverage map**: `functions_relations/coverage-map.md`
**Scope source**: `long_term.md` item #2

---

## 1. Scope Assessment

The plan covers the **full scope** described in `long_term.md` item #2:

| Topic from long_term.md | World(s) in plan | Status |
|--------------------------|-----------------|--------|
| Sets as predicates | W1 | Covered |
| Images/preimages | W8 | Covered |
| Restriction to subsets | W9 | Covered |
| Injective/surjective/bijective-on-a-set maps | W9 (InjOn, SurjOn, BijOn) | Covered |
| Relations as sets of pairs | W11 | Covered |
| Bundled equivalences (Equiv) | W17 | Covered |
| Partial equivalences | W11 (1-2 levels) | Covered |
| Subtypes | W19 | Covered |
| Countable sets | W21 | Covered |
| Encodable types | W22 | Covered |
| Equality vs equivalence vs isomorphism | W18 (dedicated world) | Covered |
| Normalizing `↥s`, `Set.MapsTo`, `Set.InjOn` | W9, W19 | Covered |
| `Equiv` | W17 | Covered |
| `Encodable` | W22 | Covered |

**No major topics are missing.**

---

## 2. Coverage Alignment

### Core uncovered items (from coverage map Section 2)

All 9 items addressed:

| Core uncovered item | Where addressed |
|---------------------|----------------|
| Set extensionality as proof move | W1 (dominant lesson), practiced W2-W5, transferred W18 |
| Image/preimage asymmetry | W8 (positive and negative, boss is injective case) |
| Quotient well-definedness | W15 (dedicated levels 3-6 of the world) |
| Equality/equivalence/isomorphism distinction | W18 (dedicated consolidation world) |
| Subtype coercion mechanics | W19 (8-10 levels with novelty management) |
| Cantor's theorem and diagonalization | W21 (preparation levels + boss) |
| Encodable | W22 (dedicated world) |
| Partial equivalence relations | W11 (1-2 levels after four main properties) |
| MapsTo, InjOn, SurjOn, BijOn | W9 (dedicated world) |

### Weakly covered items (from coverage map Section 3)

All 9 items addressed:

| Weakly covered item | Where addressed |
|---------------------|----------------|
| Indexed unions/intersections | W4 (dedicated world) |
| Set.restrict and Set.inclusion | W9 |
| Function.Involutive | W6 (1 level) |
| Partition ↔ equivalence relation (both directions) | W12 (boss covers one direction, earlier levels seed both) |
| Quotient.ind / Quotient.rec | W15 (level 7 in the sequence) |
| Equiv.Perm | W17 |
| Denumerable | W22 |
| Antisymmetric | W11 |
| Schröder-Bernstein | W22 (used as tool, not proved) |

### Example coverage gaps (from coverage map Section 4)

All required concrete examples have assigned worlds:

| Definition to concretize | Planned location |
|--------------------------|-----------------|
| Set membership (evens, odds) | W3 |
| Set operations ({1,2,3} ∩ {2,3,4}) | W3 |
| Injective ((· + 1) on ℕ) | W7 |
| Surjective (concrete function) | W7 |
| Not injective (counterexample) | W7 |
| Not surjective ((· + 1) on ℕ) | W7 |
| Equivalence relation (mod 2) | W13 |
| Not an equivalence relation (counterexamples) | W13 |
| Quotient (ℤ mod n) | W16 |
| Equiv (Fin n ≃ {i // i < n}) | W20 |
| Subtype ({n : ℕ // Even n}) | W20 |
| Countable (ℕ × ℕ) | W22 |
| Uncountable (Cantor) | W21 |
| **Image (f '' {1,2,3})** | **Not in a dedicated example world — absorbed into W8 lecture** |
| **Image/inter counterexample** | **Nominally W7 per misconception plan, but W7 is ConcreteFunctions (no image knowledge). Actually must be in W8.** |

The image/preimage cluster is the weakest in example coverage — see P2 defect #1 below.

### Recommended merges (from coverage map Section 8)

All implemented:
- PER merged into W11 (relations cluster)
- Set.prod merged into W4 (indexed families)
- Function.Involutive merged into W6

---

## 3. World Graph Issues

### Dependency ordering

All 22 worlds have sound dependency chains. No world requires material taught in a later world.

Dependency graph (verified):
- W1 → W2 → W3 (also depends on W1)
- W1, W2 → W4
- W1-W4 → W5
- W1 → W6 → W7
- W2, W6 → W8
- W6, W8 → W9
- W6-W9 → W10
- W1 → W11 → W12
- W11, W12 → W13
- W11-W13 → W14
- W12 → W15
- W15, W13 → W16
- W6 → W17
- W12, W15, W17 → W18
- W1, W6 → W19
- W19, W17 → W20
- W1, W4, W6 → W21
- W17, W21 → W22

### World type mix

| Type | Count | Worlds |
|------|-------|--------|
| Lecture | 13 | W1, W2, W4, W6, W8, W9, W11, W12, W15, W17, W19, W21, W22 |
| Example | 5 | W3, W7, W13, W16, W20 |
| Pset | 3 | W5, W10, W14 |
| Review/Consolidation | 1 | W18 |

Good mix. Each cluster (except Cluster 5) has lecture + example + pset. Cluster 5 has lecture + example but no pset — the course is nearing its end, so this is acceptable.

### Structural concern: no concrete image/preimage world

Every major topic cluster has a dedicated example world EXCEPT image/preimage:

| Topic cluster | Lecture world | Example world |
|---------------|--------------|---------------|
| Sets | W1, W2 | W3 (ConcreteSets) |
| Functions | W6 | W7 (ConcreteFunctions) |
| Image/Preimage | W8 | **None** |
| Functions on Sets | W9 | **None** (W10 is a pset, not examples) |
| Relations | W11, W12 | W13 (ConcreteRelations) |
| Quotients | W15 | W16 (ConcreteQuotients) |
| Equiv | W17 | **None** (W18 is consolidation, W20 is concrete subtypes) |
| Subtypes | W19 | W20 (ConcreteSubtypes) |
| Countability | W21, W22 | **None** (examples are within lecture worlds) |

The image/preimage gap is the most notable because:
- The coverage map identifies the image/inter counterexample as "the most important counterexample in the course"
- Concrete image computations (compute f '' {1,2,3}) are not placed in any example world
- W8 includes introductory notation levels with trivial proofs, which partially fills this gap, but they serve a novelty-management role rather than a grounding-examples role

This is not blocking (W8 can absorb these examples as levels), but it's a structural asymmetry worth noting.

---

## 4. Proof-Move Gaps

The proof-move map (PLAN Section 3) and transfer plan (PLAN Section 8) are **detailed and complete**. Every core proof move has:
- A clear introduction point
- At least two practice locations
- A retrieval location (usually a pset world)
- A transfer location (W18 or docstrings)

Specific moves verified:

| Move | Introduced | Practiced | Retrieved | Transferred |
|------|-----------|-----------|-----------|-------------|
| Set extensionality | W1 | W2, W3, W5 | W5, W10 | W18 |
| Witness exhibition (∃) | W6 | W7, W8, W12 | W10, W14 | W18 |
| Injectivity proof shape | W6 | W7, W8, W9 | W10 | W15 (mirror), W18 |
| Well-definedness | W15 | W15 (levels 4-6), W16 | W18 | Docstring |
| Diagonalization | W21 (prep levels) | W21 (boss) | — | Docstring |
| Equiv construction | W17 | W17 (multiple), W20 | — | Docstring |
| Membership chasing | W2 | W3, W4, W5, W8 | W5, W10 | — |
| Case splitting on ∨ | W2 | W3, W4, W5 | W5 | — |

**No proof-move gaps found.** The two weaker moves are:
- **Proof by contrapositive**: introduced W6, practiced W8 only. But this is "supporting" importance, so thin coverage is acceptable.
- **Diagonalization**: only in W21. But it's a specialized technique — single-world coverage is appropriate.

---

## 5. Granularity Issues

### Granularity framework

The plan's granularity framework (Section 4) is well-defined:
- One center of gravity per world
- One dominant lesson per level
- One new thing per level
- Explicit split/merge triggers
- No level count targets

### Novelty hotspots

The plan correctly identifies and mitigates all four novelty hotspots flagged by the coverage map:

| Hotspot | World | Mitigation |
|---------|-------|------------|
| Image/Preimage | W8 | Separate notation introduction from proof-move introduction; 2 levels notation-only |
| Quotients | W15 | Detailed 10-level sequence with one new API item per level |
| Subtypes | W19 | 7-level sequence: syntax → extraction → coercion → invisible coercion → conversion |
| Functions-on-Sets | W9 | MapsTo first (simplest), then InjOn (key), then SurjOn/BijOn, then restrict |

### Boss design

Every boss integrates multiple earlier moves and has identified seeded subskills. The boss map (Section 7) is thorough — 22 bosses with specific level references for seeding.

**No granularity defects found.**

---

## 6. Transfer Gaps

The transfer plan (Section 8) provides detailed 6-stage transfer paths for 6 high-value moves:

1. Set extensionality → introduced, practiced with support, practiced with less support, fresh surface form, retrieval, transfer
2. Witness exhibition → introduced, practiced, fresh surface, more surface forms, retrieval, transfer
3. Injectivity proof shape → introduced, practiced, fresh surface, another surface, retrieval, mirror image, transfer
4. Well-definedness → introduced, practiced, concrete practice, retrieval, transfer
5. Diagonalization → first appearance, preparation levels, boss, transfer
6. Equiv construction → first appearance, practiced, concrete, earlier seed, transfer

**No transfer gaps found.** This is one of the strongest parts of the plan.

---

## 7. Example Gaps

### Major definitions with concrete examples

| Definition | Concrete example planned | World |
|-----------|-------------------------|-------|
| Set membership | Evens, odds, primes | W3 |
| Set operations | {1,2,3} ∩ {2,3,4}, etc. | W3 |
| Injective | (· + 1) on ℕ | W7 |
| Surjective | Concrete surjection | W7 |
| Bijective | Negation on ℤ | W7 |
| Image | **No dedicated example world; within W8** | W8 |
| Preimage | **No dedicated example world; within W8** | W8 |
| Equivalence relation | Mod 2 on ℤ, same parity on ℕ | W13 |
| Quotient | ℤ mod n | W16 |
| Equiv | Fin n ≃ {i // i < n}, Bool ≃ Fin 2 | W20 |
| Subtype | {n : ℕ // Even n}, {n : ℕ // n < 5} | W20 |
| Countable | ℕ × ℕ | W22 |
| Uncountable | Cantor (no surjection α → Set α) | W21 |

### Counterexamples

| Statement to disprove | Counterexample planned | World |
|----------------------|----------------------|-------|
| Symmetric + transitive → reflexive | Empty relation | W13 |
| Image distributes over intersection | Specific f, A, B | W8 (within lecture) |
| Surj ∘ inj is bijective (order matters) | Specific composition | W7 |
| Antisymmetric = not-symmetric | Identity relation | W13 |
| Reflexive + symmetric → transitive | Specific relation on small type | W13 |
| Injective function has left inverse (constructively) | **Not addressed** | — |

The constructivity edge case for left inverses is a minor gap (P2 at most).

### Missing: Set.powerset

`Set.powerset` is not explicitly placed in any world. It's "supporting" importance in the coverage map but connects to Cantor's theorem conceptually. The plan's W21 (Cantor) does not require `Set.powerset` since Cantor is stated as `¬ Surjective (f : α → Set α)`. This is acceptable but a docstring in W21 should connect to the power set concept.

---

## 8. P0 Defects (Blocking)

**None.**

---

## 9. P1 Defects (High)

**None.**

The plan addresses all major topics, has complete proof-move and transfer maps, covers all core definitions with examples, has no dependency errors, and has a real transfer plan.

---

## 10. P2 Defects (Medium)

### P2-1: Misconception plan numbering error

The misconception plan (PLAN Section 9, item #2) says:

> "f '' (A ∩ B) = f '' A ∩ f '' B (false without injectivity) — **W7** (counterexample level) + W8 (positive result with injectivity)"

But W7 in the plan is **ConcreteFunctions** (injective/surjective examples on specific functions). W7 has no image/preimage knowledge — that's W8 (ImageAndPreimage). The image/inter counterexample must be a level **within W8**, not W7.

**Fix**: Change "W7 (counterexample level)" to "W8 (counterexample level within the lecture world)" in Section 9 item #2.

### P2-2: No dedicated concrete image/preimage example world

Every other major topic cluster has a dedicated example world (W3 for sets, W7 for functions, W13 for relations, W16 for quotients, W20 for subtypes). Image/preimage — one of the most important clusters — does not. The coverage map recommended:
- Compute f '' {1,2,3} under a specific function
- Concrete preimage computation
- Counterexample: f '' (A ∩ B) ≠ f '' A ∩ f '' B with specific f, A, B

These are absorbed into W8 (a lecture world). This is workable but structurally weaker than a dedicated example world.

**Fix options**:
- (Preferred) Add a W8.5 "ConcreteImages" example world (3-5 levels) between W8 and W9. This mirrors how W7 follows W6.
- (Acceptable) Explicitly plan 2-3 concrete computation levels within W8 and note in the spec that these serve a grounding/example function, not just novelty management.

### P2-3: Set.powerset not placed

`Set.powerset` is not included in any world's inventory or level plan. The coverage map recommended 1-2 levels in W2 or W4.

**Fix**: Add 1-2 levels to W4 (IndexedFamilies) covering `Set.powerset`. This connects naturally to the "set of sets" theme in W4 and provides foreshadowing for Cantor (W21).

### P2-4: Constructivity of left inverses not addressed

The coverage map flags: "Every injective function has a left inverse (constructively) — On empty domain edge case or non-constructive note." The plan covers left inverses in W6 but does not mention the constructivity issue.

**Fix**: Add a docstring warning or a dedicated level in W6 about the empty-domain edge case and the non-constructive nature of choosing left inverses.

---

## 11. Specific Recommendations (Ranked)

1. **(P2-1)** Fix misconception plan numbering: change "W7" → "W8" for the image/inter counterexample.
2. **(P2-2)** Consider adding a ConcreteImages example world (or expand W8 with explicit example levels) to match the example coverage of other clusters.
3. **(P2-3)** Add 1-2 `Set.powerset` levels to W4.
4. **(P2-4)** Add a docstring or level in W6 about left inverse constructivity.
5. **(Enhancement)** In W21, add a docstring connecting Cantor's theorem to the power set concept even if `Set.powerset` is not directly used.

---

## 12. Overall Verdict

**PASS**

This is a strong plan. It covers the full scope of `long_term.md` item #2 comprehensively across 22 worlds and ~170-190 estimated levels. The proof-move map is detailed with clear introduction → practice → retrieval → transfer paths for all core moves. The transfer plan provides 6-stage paths for 6 high-value moves. The granularity framework is well-defined with explicit novelty hotspot mitigations. The inventory release plan is thorough with global disables, per-world unlocks, and identified exploit vectors. The boss map integrates multiple earlier moves with identified seeded subskills.

The defects found are P2-level (misconception numbering error, missing concrete image example world, missing powerset placement, constructivity edge case). None would waste downstream work. All can be addressed during authoring or with minor plan amendments.

The plan is ready for Phase 2 (world authoring).
