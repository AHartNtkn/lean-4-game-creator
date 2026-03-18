# Plan Review: Functions & Relations

**Reviewer**: Plan review (manual)
**Date**: 2025-03-18
**Plan reviewed**: `lean4game-functions-relations/PLAN.md`
**Coverage map**: `functions_relations/coverage-map.md`
**Scope source**: `long_term.md` Course #2

---

## 1. Scope Assessment

The plan covers the **full scope** described in `long_term.md` for Course #2:

| Topic from long_term.md | Where covered |
|--------------------------|---------------|
| Sets as predicates | W1 |
| Images/preimages | W8 |
| Restriction to subsets | W10 (Set.restrict, Set.inclusion) |
| Injective/surjective/bijective-on-a-set maps | W10 (MapsTo, InjOn, SurjOn, BijOn) |
| Relations as sets of pairs | W12 (as `α → α → Prop`, mathlib's encoding) |
| Bundled equivalences | W18 (Equiv) |
| Partial equivalences | W12 (1–2 levels on PER) |
| Subtypes | W20 |
| Countable sets | W22 |
| Encodable types | W23 |
| Equality vs equivalence vs isomorphism | W19 (dedicated consolidation world) |
| Working with `↥s` | W20 |
| `Set.MapsTo` | W10 |
| `Set.InjOn` | W10 |
| `Equiv` | W18 |
| `Encodable` | W23 |

**No major topics from long_term.md are missing.** The plan is not a shallow survey — it goes deep, with 23 worlds covering all required material plus examples and psets.

---

## 2. Coverage Alignment

### Core uncovered items from coverage map → plan

All 9 core uncovered items from the coverage map are addressed:

1. **Set extensionality as a proof move** → W1 (introduced), W2/W3/W5/W8 (practiced), W19 (transferred). Full 6-stage transfer plan in Section 8.
2. **Image/preimage asymmetry** → W8 (positive result: injective image intersection as boss), W9 (counterexample as boss).
3. **Quotient well-definedness** → W16 (dedicated levels 3–6 in the 10-level novelty-managed sequence).
4. **Equality/equivalence/isomorphism distinction** → W19 (dedicated consolidation world).
5. **Subtype coercion mechanics** → W20 (dedicated 8-level novelty-managed sequence).
6. **Cantor's theorem and diagonalization** → W22 (preparation levels + boss, with explicit seeding plan).
7. **Encodable** → W23 (dedicated world).
8. **Partial equivalence relations** → W12 (1–2 levels after the four main properties).
9. **MapsTo/InjOn/SurjOn/BijOn** → W10 (dedicated world).

### Weakly covered items from coverage map → plan

All 9 weakly covered items are addressed:

1. **Indexed unions/intersections** → W4 (dedicated world + application in W22).
2. **Set.restrict, Set.inclusion** → W10.
3. **Function.Involutive** → W6 (included in center of gravity).
4. **Partition ↔ equivalence relation** → W13 (both directions as proof-move goals, one direction as boss).
5. **Quotient.ind / Quotient.rec** → W16 (level 7 in sequence).
6. **Equiv.Perm** → W18.
7. **Denumerable** → W23.
8. **Antisymmetric** → W12.
9. **Schröder-Bernstein** → W23 (used as tool, not proved from scratch).

### Example coverage

All 18 "required concrete examples" from the coverage map are covered:

- Set membership examples → W3
- Set operations on specific sets → W3
- Injective/surjective/non-injective/non-surjective functions → W7
- Image computations → W9
- Image/intersection counterexample → W9
- Equivalence relation (mod 2) → W14
- Non-equivalence-relation counterexamples → W14
- Concrete quotient (ℤ mod n) → W17
- Concrete Equiv → W21
- Concrete subtype → W21
- ℕ × ℕ countable → W23 boss
- Cantor diagonal → W22

All 4 critical counterexamples from the coverage map are addressed:

1. Symmetric + transitive ≠ reflexive → W14 (empty relation)
2. Image ∩ failure → W9 (boss: most important counterexample in the course)
3. Composition order matters → W7
4. Left inverse constructivity → W6 (docstring/note only — see P2 below)

**No example coverage gaps identified.**

---

## 3. World Graph Issues

### Dependencies

All 23 world dependencies are sound. No world requires material taught later.

Dependency trace verified:
- Cluster 1 (W1–W5): W1→W2→W3, W1+W2→W4, W1–W4→W5 ✅
- Cluster 2 (W6–W11): W1→W6→W7, W2+W6→W8→W9, W6+W8→W10, W6–W10→W11 ✅
- Cluster 3 (W12–W15): W1→W12→W13, W12+W13→W14, W12–W14→W15 ✅
- Cluster 4 (W16–W19): W13→W16, W16+W14→W17, W6→W18, W13+W16+W18→W19 ✅
- Cluster 5 (W20–W23): W1+W6→W20, W20+W18→W21, W1+W4+W6→W22, W18+W22→W23 ✅

### World type mix

| Cluster | Lectures | Examples | Psets | Review |
|---------|----------|----------|-------|--------|
| 1 (Sets) | W1, W2, W4 | W3 | W5 | — |
| 2 (Functions) | W6, W8, W10 | W7, W9 | W11 | — |
| 3 (Relations) | W12, W13 | W14 | W15 | — |
| 4 (Quotients+Equiv) | W16, W18 | W17 | — | W19 |
| 5 (Subtypes+Countability) | W20, W22, W23 | W21 | **None** | **None** |

**Cluster 5 has no pset or review world.** This is the only cluster without retrieval practice. See P1-1 below.

### Structural coherence

Each world has a clearly identified single center of gravity. The plan is explicit about split triggers, merge triggers, and novelty management for hotspot worlds (W8, W16, W20). Example worlds are correctly placed after their lecture worlds. The world graph is well-structured.

---

## 4. Proof-Move Gaps

The proof-move map (Section 3) identifies 20 proof moves, each with introduction, practice, and transfer locations. Section 8 provides detailed 4–7 stage transfer plans for the 6 highest-value moves.

**No proof moves are listed but not actually taught.** Each has at least: introduction in a lecture world, practice in a subsequent world, and some form of retrieval in a pset/boss.

Minor observations:

- The proof-move map table in Section 3 shows "—" in the transfer column for well-definedness, diagonalization, funext, and case-building. Section 8 provides transfer text for well-definedness and diagonalization. The table's "—" entries are inconsistent with Section 8 — not a content gap, just a formatting inconsistency.
- "Induction on ℕ for countability" is listed as introduced W22, practiced W23. But W23's spec (Encodability) doesn't explicitly include induction practice in its proof-move goals. See P2-2.

---

## 5. Granularity Issues

### Granularity framework

The plan's granularity framework (Section 4) is well-defined: one center of gravity per world, one dominant lesson per level, one new thing per level, explicit split/merge triggers, no level count targets. All 23 worlds pass the single-center-of-gravity test.

### Novelty management

The plan correctly identifies and mitigates 5 novelty hotspots:
- W8 (image/preimage): notation before proof moves ✅
- W16 (quotients): 10-level sequence, one new API item per level ✅
- W20 (subtypes): 8-level sequence with explicit coercion teaching ✅
- W10 (functions on sets): MapsTo first, then InjOn ✅
- W2 (set operations): ext is dominant lesson, push_neg gets its own level ✅

### W12 boss granularity

The W12 boss description offers two alternatives without committing: "Prove that the composition of two transitive relations need not be transitive — or prove a multi-step transitivity chain using `calc`."

Problems:
1. A counterexample as a lecture world boss is unusual; counterexamples belong in W14.
2. The calc option only tests transitivity, ignoring the world's other main topics (reflexivity, symmetry, antisymmetry, PER).
3. The "or" phrasing defers a decision that should be made at plan time.

See P1-2.

---

## 6. Transfer Gaps

Section 8 provides detailed transfer plans for 6 high-value moves:

1. **Set extensionality**: 6 stages — introduced → practiced with support → less support → fresh surface form → retrieval → transfer ✅
2. **Witness exhibition**: 7 stages ✅
3. **Injectivity proof shape**: 7 stages including "mirror image" (well-definedness is the dual) ✅
4. **Well-definedness**: 5 stages ✅
5. **Diagonalization**: 4 stages ✅
6. **Constructing Equiv**: 5 stages ✅

**No high-value move completely lacks a transfer plan.** Diagonalization has no retrieval beyond W22, but it's a specialized technique — single-world coverage is appropriate.

---

## 7. Example Gaps

Every major definition in the course has at least one planned concrete example in a dedicated example world:

| Definition | Example world | Examples planned |
|-----------|--------------|-----------------|
| Set membership | W3 | Evens, odds, primes |
| Set operations | W3 | {1,2,3} ∩ {2,3,4}, complement of evens, de Morgan on specific sets |
| Injective/Surjective | W7 | (·+1), (·*2) on ℕ, negation on ℤ |
| Image/Preimage | W9 | f '' {1,2,3}, f ⁻¹' {2,4,6}, image/inter counterexample (boss) |
| Equivalence relation | W14 | Mod 2, same parity, empty relation, ≤ on ℕ |
| Quotient | W17 | ℤ mod 2, ℤ mod 3, well-def failure |
| Equiv | W21 | Bool ≃ Fin 2, Fin n ≃ {i // i < n} |
| Subtype | W21 | {n : ℕ // Even n}, {n : ℕ // n < 5} |
| Countable/Uncountable | W22/W23 | Cantor (W22 boss), ℕ × ℕ (W23 boss) |

Counterexamples: symmetric+transitive≠reflexive (W14), reflexive+symmetric≠transitive (W14), image∩ failure (W9), composition order matters (W7), antisymmetric≠not-symmetric (W14).

**No major definition lacks a concrete example.**

One gap: Cluster 5 has no example world between W22 (Countability lecture) and W23 (Encodability lecture). Concrete countability/encodability examples (Is ℤ countable? Encode a specific pair.) are within the lecture worlds rather than dedicated example worlds. See P2-3.

---

## 8. P0 Defects (blocking)

**None.**

The plan has no fundamental structural problems that would waste downstream work:
- All major topics from long_term.md are present.
- The proof-move map is present and substantive.
- The world graph has no dependency errors.
- The transfer plan exists and covers high-value moves.
- All major definitions have example plans.
- The coverage map's findings are systematically addressed.

---

## 9. P1 Defects (high)

### P1-1: No pset/retrieval world for Cluster 5 (Subtypes + Countability)

Every other cluster has a pset world (W5 for Sets, W11 for Functions, W15 for Relations) or a review world (W19 for Quotients+Equiv). Cluster 5 has four worlds of new material (W20 lecture, W21 example, W22 lecture, W23 lecture) with no retrieval practice.

After the longest uninterrupted stretch of new material in the course, the learner has no opportunity to practice choosing the right technique from the full W20–W23 toolkit without scaffolding. This violates the plan's own established pattern of lecture-example-pset cycles.

**Recommendation**: Add a W24 pset or consolidation world after W23 that integrates subtypes, countability, and encodability. Problems should require choosing between subtype construction, countability arguments, and encoding constructions without prompting. This also provides a natural location for a final boss that brings together the course's main themes.

### P1-2: W12 (BinaryRelations) boss is underspecified and poorly chosen

The boss offers two alternatives without committing: "Prove that the composition of two transitive relations need not be transitive — or prove a multi-step transitivity chain using calc."

Problems:
1. **Counterexample as a lecture boss is wrong.** Counterexamples belong in W14 (ConcreteRelations), the example world. Lecture bosses should prove a general theorem that integrates the world's main moves.
2. **The calc option only tests transitivity.** The world teaches reflexivity, symmetry, transitivity, antisymmetry, and PER — the boss should integrate multiple properties, not just one.
3. **The "or" phrasing defers a decision.** Plan-level boss descriptions should commit to a specific integrative challenge.

**Recommendation**: Replace with a boss that integrates multiple relation properties. For example: "Prove that if R is a PER (symmetric + transitive), then R is reflexive on its domain `{x | R x x}`." This integrates PER (which the world introduces), the symmetry+transitivity interaction, and definition-unfolding. It's a genuine theorem, not a counterexample.

---

## 10. P2 Defects (medium)

### P2-1: Constructivity of left inverses addressed only by docstring

The coverage map flags "Every injective function has a left inverse (constructively)" as a critical edge case. The plan (W6) addresses this only with a docstring about `Classical.choice`. A dedicated level — even a simple one where the learner sees `Function.invFun` requires `Classical.choice`, or tries to construct a left inverse and encounters the non-constructivity — would make this concrete rather than expository.

### P2-2: "Induction on ℕ for countability" practice claim not backed by W23 spec

The proof-move map says this move is introduced in W22 and practiced in W23. But W23's world spec (Encodability) focuses on Encodable/Denumerable/Schröder-Bernstein. None of W23's described proof-move goals mention induction practice. The practice opportunity may not materialize during authoring unless the world author is alerted.

**Recommendation**: Add an explicit note in W23's proof-move goals that at least one level should use ℕ induction for an encoding construction.

### P2-3: Two back-to-back lecture worlds in Cluster 5 with no example world between them

W22 (Countability) and W23 (Encodability) are both lecture worlds with no dedicated example world. Every other lecture pair has a dedicated example world (W3 for W1/W2, W7 for W6, W9 for W8, W14 for W12/W13, W17 for W16, W21 for W20). This is partially mitigated by W22's Cantor boss and W23's ℕ×ℕ boss both being concrete, but there are no levels dedicated to concrete countability exercises ("is ℤ countable?", "is a finite set countable?", "encode a specific pair").

**Recommendation**: This overlaps with P1-1 — a combined pset+example world (W24) could address both the missing retrieval practice and the missing concrete countability/encodability examples.

### P2-4: Proof-move map table (Section 3) has "—" entries inconsistent with Section 8

The table shows "—" for transfer of well-definedness, diagonalization, funext, and case-building. Section 8 provides transfer text for well-definedness and diagonalization. Minor formatting inconsistency.

**Recommendation**: Update the Section 3 table to match Section 8.

---

## 11. Specific Recommendations (ranked)

1. **(P1-1)** Add a W24 pset/consolidation world for Cluster 5. Integrate subtypes, countability, and encodability problems. Include concrete examples. This is the most significant structural gap.

2. **(P1-2)** Replace W12's boss with one that integrates reflexivity, symmetry, transitivity, and PER — such as "a PER is reflexive on its domain." Remove the non-committal "or" phrasing.

3. **(P2-3)** The W24 from recommendation #1 can also absorb concrete countability/encodability examples, addressing the two-back-to-back-lectures gap.

4. **(P2-2)** Add explicit ℕ-induction practice to W23's proof-move goals.

5. **(P2-1)** Upgrade the left-inverse constructivity treatment from docstring to a dedicated level in W6 or W7.

6. **(P2-4)** Update Section 3 proof-move map table to match Section 8.

---

## 12. Overall Verdict: PASS

The plan is thorough, well-structured, and covers the full scope of the course as described in long_term.md. The proof-move map is present and substantive with 20 identified moves, each with introduction, practice, and transfer points. The world graph has no dependency errors. All major definitions have concrete example plans across 6 dedicated example worlds. The transfer plan covers 6 high-value moves with multi-stage progressions. The inventory release plan and exploit mitigation are informed by lessons learned from other courses. The misconception plan identifies 13 specific misconceptions with concrete addressing strategies. The granularity framework is well-defined with 5 novelty hotspots explicitly mitigated.

The P1 defects (missing Cluster 5 retrieval world, underspecified W12 boss) are significant but not plan-breaking — they can be fixed with targeted amendments before authoring begins. No P0 defects were found.

**The plan is ready for world authoring after the P1 defects are addressed.**
