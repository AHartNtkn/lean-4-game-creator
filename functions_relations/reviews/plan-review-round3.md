# Plan Review: Functions & Relations (Round 3)

**Reviewer**: Plan review skill (fresh context)
**Date**: 2026-03-18
**Plan reviewed**: `lean4game-functions-relations/PLAN.md`
**Coverage map**: `functions_relations/coverage-map.md`
**Scope source**: `long_term.md` Course #2
**Prior reviews**: Round 1 found 2 P1 + 4 P2 defects. Plan was amended. Round 2 confirmed PASS.

---

## 1. Scope Assessment

The plan covers the **full scope** described in `long_term.md` for Course #2.

| Topic from long_term.md | Where covered | Status |
|--------------------------|---------------|--------|
| Sets as predicates | W1 | Covered |
| Images/preimages | W8 | Covered |
| Restriction to subsets | W10 (Set.restrict, Set.inclusion) | Covered |
| Injective/surjective/bijective-on-a-set maps | W10 (MapsTo, InjOn, SurjOn, BijOn) | Covered |
| Relations as sets of pairs | W12 (as `α → α → Prop`) | Covered |
| Bundled equivalences | W18 (Equiv) | Covered |
| Partial equivalences | W12 (1–2 levels on PER) | Covered |
| Subtypes | W20 | Covered |
| Countable sets | W22 | Covered |
| Encodable types | W23 | Covered |
| Equality vs equivalence vs isomorphism | W19 (dedicated consolidation world) | Covered |
| Working with `↥s` | W20 | Covered |
| `Set.MapsTo`, `Set.InjOn` | W10 | Covered |
| `Equiv` | W18 | Covered |
| `Encodable` | W23 | Covered |

**No major topics from long_term.md are missing.** The plan is not a shallow survey — it goes deep across 24 worlds.

---

## 2. Coverage Alignment

### Core uncovered items (coverage map Section 2) → plan

All 9 core uncovered items are addressed:

| Core uncovered item | Where addressed | Adequacy |
|---------------------|----------------|----------|
| Set extensionality as proof move | W1 (introduced), W2/W3/W5/W8 (practiced), W19 (transferred) | Full 6-stage transfer plan in Section 8 |
| Image/preimage asymmetry | W8 (positive: injective image-∩ as boss), W9 (negative: counterexample as boss) | Both directions covered |
| Quotient well-definedness | W16 (levels 3–6 in 10-level novelty-managed sequence) | Central focus of the world |
| Equality/equivalence/isomorphism distinction | W19 (dedicated consolidation world) | Explicitly required by course description |
| Subtype coercion mechanics | W20 (8-level novelty-managed sequence) | Hotspot identified and mitigated |
| Cantor's theorem and diagonalization | W22 (preparation levels + boss, with seeding plan) | Seeded step-by-step |
| Encodable | W23 (dedicated world) | Full world with ℕ-induction practice |
| Partial equivalence relations | W12 (1–2 levels + boss integrates PER) | PER reflexivity-on-domain as boss |
| MapsTo/InjOn/SurjOn/BijOn | W10 (dedicated world) | All four + restrict + inclusion |

### Weakly covered items (coverage map Section 3) → plan

All 9 addressed:
- Indexed unions/intersections → W4
- Set.restrict, Set.inclusion → W10
- Function.Involutive → W6
- Partition ↔ equivalence relation → W13 (both directions)
- Quotient.ind → W16 (level 7)
- Equiv.Perm → W18
- Denumerable → W23
- Antisymmetric → W12
- Schröder-Bernstein → W23 (used as tool, not proved)

### Example coverage

All 18 "required concrete examples" from the coverage map are addressed across 6 dedicated example worlds (W3, W7, W9, W14, W17, W21) plus concrete bosses in lecture worlds (W22, W23).

All 4 critical counterexamples are addressed:
1. Symmetric + transitive ≠ reflexive → W14 (empty relation)
2. Image ∩ failure → W9 boss
3. Composition order matters → W7
4. Left-inverse constructivity → W6 (upgraded from docstring to dedicated level)

**No coverage gaps identified.**

---

## 3. World Graph Issues

### Dependencies

All 24 world dependencies are sound. Verified forward-pointing with no cycles:

- Cluster 1: W1→W2→W3, W1+W2→W4, W1–W4→W5
- Cluster 2: W1→W6→W7, W2+W6→W8→W9, W6+W8→W10, W6–W10→W11
- Cluster 3: W1→W12→W13, W12+W13→W14, W12–W14→W15
- Cluster 4: W13→W16, W16+W14→W17, W6→W18, W13+W16+W18→W19
- Cluster 5: W1+W6→W20, W20+W18→W21, W1+W4+W6→W22, W18+W22→W23, W20–W23→W24

No world depends on material taught later.

### World type mix

| Cluster | Lectures | Examples | Psets | Review |
|---------|----------|----------|-------|--------|
| 1 (Sets) | W1, W2, W4 | W3 | W5 | — |
| 2 (Functions) | W6, W8, W10 | W7, W9 | W11 | — |
| 3 (Relations) | W12, W13 | W14 | W15 | — |
| 4 (Quotients+Equiv) | W16, W18 | W17 | — | W19 |
| 5 (Subtypes+Count.) | W20, W22, W23 | W21 | W24 | — |

Every cluster has at least one lecture, one example, and one pset/review world. W24 (added after round 1 review) fixes the Cluster 5 gap.

### Structural coherence

Each world has a clearly identified single center of gravity. No world has two unrelated theorem families. Example worlds follow their lecture worlds. Pset worlds follow their clusters.

---

## 4. Proof-Move Gaps

The proof-move map (Section 3) identifies 20 proof moves, each with introduction, practice, and (where appropriate) transfer locations. Section 8 provides detailed 4–7 stage transfer plans for 6 high-value moves:

1. Set extensionality (6 stages)
2. Witness exhibition (7 stages)
3. Injectivity proof shape (7 stages, including "mirror image" — well-definedness as dual)
4. Well-definedness (5 stages)
5. Diagonalization (4 stages)
6. Constructing Equiv (5 stages)

**No proof moves are listed but not actually taught.** Each has introduction in a lecture world and practice in a subsequent world.

The Section 3 table shows "—" in the transfer column for funext, antisymmetry, case-building, and ℕ-induction. These are lower-value or specialized moves where single-world coverage is appropriate. This is correct, not a gap.

---

## 5. Granularity Issues

### Framework

The granularity framework (Section 4) is well-defined:
- One center of gravity per world
- One dominant lesson per level
- One new thing per level
- Explicit split and merge triggers
- No level count targets

All 24 worlds pass the single-center-of-gravity test.

### Novelty management

The plan identifies and mitigates 5 novelty hotspots with explicit level sequences:
- W8 (image/preimage): notation before proof moves
- W16 (quotients): 10-level sequence, one new API item per level
- W20 (subtypes): 8-level sequence with explicit coercion teaching
- W10 (functions on sets): MapsTo first, then InjOn pattern
- W2 (set operations): ext stays from W1, push_neg gets own level

### Observation: W4 and W6 lack explicit novelty sequences

W4 introduces 6 definitions (⋃, ⋂, sUnion, sInter, Set.prod, Set.powerset) plus 3 new notations in one world. W6 introduces 6+ definitions plus 2 new tactics (funext, congr). Both are within the 8–11 level estimate, and the one-new-thing-per-level rule bounds the introduction rate. However, unlike W8/W16/W20, neither W4 nor W6 has an explicit level-by-level novelty management sequence in the plan. See P2-1.

### Boss seeding

The boss map (Section 7) specifies seeded subskills for all 24 bosses. Every boss lists the earlier levels that seed its required moves.

---

## 6. Transfer Gaps

Section 8 provides multi-stage transfer plans for 6 high-value moves. Four pset worlds (W5, W11, W15, W24) and one review world (W19) provide retrieval practice. Transfer text is included for each high-value move ("In ordinary math: ...").

**No high-value move lacks a transfer plan.** Diagonalization is specialized enough that single-world coverage is appropriate.

---

## 7. Example Gaps

Every major definition has at least one planned concrete example:

| Definition | Example world | Examples |
|-----------|--------------|----------|
| Set membership | W3 | Evens, odds, primes, {1,2,3} |
| Set operations | W3 | ∩, ∪, ᶜ on specific sets |
| Injective | W7 | (·+1) on ℕ, (·*2) on ℕ |
| Surjective | W7 | Concrete surjection |
| Not injective/surjective | W7 | Counterexample witnesses |
| Image/Preimage | W9 | f '' {1,2,3}, f ⁻¹' {2,4,6} |
| Image ∩ failure | W9 | Boss: most important counterexample |
| Equivalence relation | W14 | Mod 2, same parity |
| Non-equivalence | W14 | Empty relation, refl+symm but not trans |
| Quotient | W17 | ℤ mod 2, ℤ mod 3 |
| Equiv | W21 | Bool ≃ Fin 2, Fin n ≃ {i // i < n} |
| Subtype | W21 | {n // Even n}, {n // n < 5} |
| Countable | W22/W23/W24 | Cantor, ℕ × ℕ, ℤ, finite types |

5 critical counterexamples planned: sym+trans≠refl (W14), image∩ failure (W9), composition order (W7), refl+sym≠trans (W14), antisymmetric≠not-symmetric (W14).

**No major definition lacks a concrete example.**

---

## 8. P0 Defects (blocking)

**None.**

- All major topics from long_term.md are present
- The proof-move map is present with 20 moves and 6 detailed transfer plans
- The world graph has no dependency errors
- The transfer plan exists and covers high-value moves
- All major definitions have example plans
- The coverage map's findings are systematically addressed

---

## 9. P1 Defects (high)

**None.**

The two P1 defects from round 1 have been fixed:
- P1-1 (missing Cluster 5 retrieval): W24 added as pset/consolidation world
- P1-2 (underspecified W12 boss): Committed to PER reflexivity-on-domain theorem, integrates symmetry + transitivity + PER + definition-unfolding

---

## 10. P2 Defects (medium)

### P2-1: W4 and W6 lack explicit novelty management sequences

W4 introduces 6 definitions + 3 notations. W6 introduces 6+ definitions + 2 tactics. Both are within estimated level counts (8–11 and 9–11 respectively), and the one-new-thing-per-level rule bounds the introduction rate. But unlike W8, W16, and W20 (which have explicit step-by-step level sequences in their world specs), W4 and W6 leave the level ordering to the world author without guidance.

This is a low-risk gap — the world author can sequence these correctly using the plan's granularity framework. But explicit sequences for W4 and W6 would strengthen the spec, especially since W4's powerset+prod+indexed-ops combination and W6's injectivity+surjectivity+inverses+funext combination are non-trivial to order.

### P2-2: simp enablement scope after W2 is ambiguous

Section 6 says simp is disabled in W1 and enabled midway through W2 with "set lemmas only." The per-world unlock table doesn't mention simp again for W3–W24. The implication is that simp stays enabled from W2 onwards, but it's not explicitly stated whether `simp` is globally available or whether some worlds should re-restrict it. In worlds like W12 (relations) and W16 (quotients), `simp` with relation/quotient lemmas could short-circuit intended proofs.

The plan's exploit vector section covers this at the tactic level (`tauto`, lattice lemmas) but not the `simp` lemma family level. This is an authoring-level detail rather than a plan defect — world authors will need to decide per-level which `simp` lemmas to allow. But a one-line note clarifying "simp remains enabled from W2 onwards; world authors must disable specific simp lemmas per-level when they short-circuit intended proof shapes" would remove ambiguity.

---

## 11. Specific Recommendations (ranked)

1. **(P2-1)** Add explicit novelty management sequences for W4 and W6, similar to the sequences already written for W8, W16, and W20. For W4: suggest ordering as ⋃ → ⋂ → sUnion/sInter (briefly) → Set.prod → powerset. For W6: suggest ordering as Injective → Surjective → composition → Bijective → inverses → Involutive → funext → constructivity.

2. **(P2-2)** Add a one-line note to Section 6 clarifying that `simp` remains enabled from W2 onwards and world authors must disable per-level `simp` lemmas when they short-circuit intended proof moves.

---

## 12. Overall Verdict: PASS

The plan is thorough, well-structured, and covers the full scope of Course #2 as described in `long_term.md`. Specific strengths:

- **24 worlds** covering all required material with sound dependency ordering
- **20 proof moves** mapped with introduction, practice, and transfer points
- **6 detailed transfer plans** (4–7 stages each) for high-value moves
- **6 dedicated example worlds** with concrete examples for every major definition
- **5 counterexample plans** targeting the course's most important misconceptions
- **13 misconceptions** mapped to specific addressing strategies
- **Comprehensive inventory release plan** with exploit mitigation informed by prior course experience (lattice aliases, tauto, simp, etc.)
- **Boss map** with seeding plans for all 24 bosses
- **Risk analysis** with 8 identified risks and mitigations
- **Granularity framework** with 5 novelty hotspots explicitly mitigated

The P1 defects from round 1 (missing Cluster 5 retrieval world, underspecified W12 boss) have been fixed. The two remaining P2 defects (missing novelty sequences for W4/W6, simp scope ambiguity) are minor and can be addressed during authoring without plan amendments.

**The plan is ready for world authoring.**
