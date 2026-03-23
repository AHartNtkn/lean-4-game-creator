# Plan Review (Round 2): functions_relations

**Date**: 2026-03-23
**Plan reviewed**: `functions_relations/PLAN.md`
**Coverage map**: `functions_relations/coverage-map.md`
**Course description (long_term.md)**: Course 2 — "Sets, functions, relations, equivalences, subtypes, and countability"
**Prior review**: `plan-review-round1.md` (FAIL — 4 P1 defects)

---

## Round 1 P1 Fix Verification

### P1 #1: Binary relation as `Set (α × α)` — illusory coverage

**Status: FIXED.**

W15 now includes:
- L07: Relations as `Set (α × α)`. Learner restates the mod-3 relation as `{p : ℕ × ℕ | p.1 % 3 = p.2 % 3}`, proves membership, and sees `Set.diagonal` as the equality relation.
- L08: Translation between representations. Learner proves reflexivity of `R : α → α → Prop` is equivalent to `Set.diagonal ⊆ {p | R p.1 p.2}`.

The item now has real introduction and supported practice. See P2 #1 below for a remaining nuance about the closure table.

### P1 #2: `Denumerable` weak closure

**Status: FIXED.**

- W25 boss (L09) now explicitly includes `Denumerable.eqv` — the learner uses it to obtain the explicit `ℕ ≃ ℕ × ℕ` equivalence.
- W27 L03 provides retrieval on a fresh type: "Prove `Denumerable ℤ`, then use `Denumerable.eqv` to obtain the explicit `ℤ ≃ ℕ` equivalence and verify a round-trip property."
- The coverage closure table now shows all 5 stages: I(W25), S(W25), R(W27), G(W25 boss), T(W27).

### P1 #3: W17 L06 introduces `≃` before Equiv is taught

**Status: FIXED.**

W17 boss (L06) no longer mentions `quotientKerEquivRange` or `≃`. The boss is now: "Given a surjective function `f : α → β`, lift a function `g : α → γ` through `Quotient (Setoid.ker f)`, prove well-definedness, and use `Quotient.inductionOn` to show a property of the lifted function." Pure lift + well-definedness + induction — no Equiv dependency.

The first isomorphism theorem content has been moved to W28 L01–L02, where Equiv has already been taught. See P2 #2 below for a residual inventory issue.

### P1 #4: Missing non-reflexive counterexample

**Status: FIXED.**

W15 L06: "Prove `¬ Reflexive (· ≠ · : ℕ → ℕ → Prop)`. Lesson: counterexample — `0 ≠ 0` is false." The three-property counterexample framework is now complete: non-symmetry (L04: `≤`), non-transitivity (L05), and non-reflexivity (L06: `≠`).

---

## Round 1 P2 Fix Verification

### P2 #1: W04 diffuse center of gravity

**Status: ADDRESSED with rationale.** W04 now includes an explicit "Center of gravity rationale" explaining why products, nonempty, and powerset are grouped with indexed operations: they all represent "compound set constructions beyond binary ∪/∩/ᶜ/\." The rationale argues that splitting would create worlds too small to sustain a coherent introduction-practice-boss arc. This is a defensible judgment call.

### P2 #2: `Set.Nonempty` missing boss integration

**Status: FIXED.** W07 boss now includes: "additionally prove `Set.Nonempty s → Set.Nonempty (f '' s)`." Nonemptiness is now integrated into a boss.

### P2 #3: `Encodable` missing transfer

**Status: FIXED.** W27 L04: "Construct an `Encodable` instance for a fresh type (e.g., `Option ℕ` or a sum type) by supplying explicit `encode`/`decode` functions." The coverage closure table now shows T=W27 for `Encodable`.

### P2 #4: `rintro`/`rcases` not explicitly taught

**Status: FIXED.** W07 L03 is now a dedicated teaching level: "Re-prove the L02 result using `rintro ⟨x, hx, rfl⟩` to destructure the image membership hypothesis in one step. Lesson: `rintro` combines `intro` and pattern matching; `rcases` does the same on existing hypotheses." Both tactics are marked "Taught" in the inventory release plan with `TacticDoc` entries.

---

## 1. Scope Completeness

All major topics from `long_term.md` course 2 are covered:

- Sets as predicates: W01–W05
- Images/preimages: W06–W08
- Injective/surjective/bijective maps: W09–W12
- Restriction to subsets: W13–W14
- Relations as predicates AND as sets of pairs: W15
- Bundled equivalences and partial equivalences: W22–W23
- Subtypes and coercions: W21
- Quotients and equivalence relations: W15–W19
- Countable sets and encodable types: W25–W27
- Equality vs equivalence vs isomorphism: W20
- Partition-equivalence correspondence: W19

**Verdict: No scope gaps.**

---

## 2. Coverage Map Alignment

All 19 core items from Section 2 of the coverage map are covered in the world graph. The "Needs architect judgment" items from the coverage map are all resolved with sound decisions.

The Example Plan (Section 3 of coverage map) is well-represented. Key concrete examples appear at appropriate points in level sketches.

**Verdict: Strong alignment.**

---

## 3. World Graph Coherence

28 worlds across 8 phases. Each phase builds on the previous. Dependencies are sound — no world depends on material taught later (the W17/Equiv issue from round 1 is fixed).

Every lecture phase has a corresponding pset:
- W01–W04 → W05 (PsetSets)
- W06–W07 → W08 (PsetImgPreimg)
- W09–W11 → W12 (PsetFunctions)
- W13 → W14 (PsetRestricted)
- W15–W17 → W18 (PsetRelations)
- W21–W23 → W24 (PsetTypesEquiv)
- W25–W26 → W27 (PsetCountability)

World type mix: 19 lecture, 7 pset, 1 example/review (W20), 1 capstone (W28).

**Verdict: Sound.**

---

## 4. Proof-Move Coverage

The proof-move coverage table (Section 5, "Proof Moves" subsection) is explicit and complete. All 16 core proof moves have all 5 stages (I, S, R, G, T) filled.

Bosses integrate multiple proof moves as designed. Spot-checked:
- W03 boss: ext + ↔ + case analysis on ∨ + combining ∧/∨
- W07 boss: image witness + preimage unfold + surjectivity + nonemptiness
- W17 boss: lift + well-definedness + inductionOn
- W28 boss: partition ↔ equivalence round-trip

**Verdict: Strong.**

---

## 5. Granularity Plan

Level sketches respect the one-new-burden-per-level constraint. Each level has a clearly identified dominant lesson.

W15 is the largest world at 11 levels. This is acceptable given it covers: three positive property checks, three negative counterexamples, the Set (α × α) representation and translation, bundling into Equivalence, a second equivalence example, and a boss. Each level has a single lesson.

Boss map (Section 7) is detailed and accurate. Every boss lists its integrated subskills and source levels.

**Verdict: Sound.**

---

## 6. Coverage Closure

The coverage closure table (Section 5 of PLAN.md) was verified against the level sketches. Core items with strong closure (all 5 stages present and real):

- All set items: `Set α`, `∈`, `⊆`, `∅`/`univ`, `setOf`, `∪`/`∩`, `ᶜ`/`\`, `Set.prod`, `Set.image`, `Set.preimage`, `Set.range`, `⋃`/`⋂`, `Set.Nonempty`
- All function items: `Injective`, `Surjective`, `Bijective`, `LeftInverse`, `RightInverse`, composition, extraction, all on-set variants
- All relation items: `Equivalence`, `Setoid`, `Setoid.ker`, `Quotient`, `Quotient.sound`/`exact`, `Quotient.lift`, `Setoid.classes`, `IsPartition`, partition-equivalence bijection
- All type/encodability items: `Subtype`, `↥s`, `Equiv`, `Countable`, `Encodable`, `Denumerable`, `Set.Countable`, countability closure, Cantor's theorem
- All core proof moves

**Items needing attention** (see P2 defects below):
- Binary relation as `Set (α × α)`: I and S are strong (W15 L07–L08). The closure table claims R=W18 and T=W18, but W18 levels don't explicitly exercise the `Set (α × α)` representation.
- `Quotient.map`: only I and S (W17). No R, G, or T. This is supporting, not core, so acceptable.

**Verdict: No illusory or weak closure on core items. All core items have real 5-stage coverage.**

---

## 7. Transfer Plan

The transfer and retrieval plan (Section 8) covers 9 high-value moves with explicit chains from first appearance through fresh surface form to plain-language transfer statement. The pset worlds use fresh types and abstract contexts.

W28 (Finale) provides cross-theme transfer:
- L01: First isomorphism theorem (functions + quotients + equivs)
- L03: InjOn + image reasoning
- L04: Cantor + function properties
- L05: BijOn → Equiv between subtypes (sets + functions + subtypes + equivs)
- L06: Partition ↔ equivalence round-trip

**Verdict: Transfer plan is present and substantive.**

---

## 8. Inventory Release Plan

The release plan (Section 6) is thorough:
- Tactics released with clear rationale and TacticDoc entries
- Baseline disabled tactics specified
- Per-world disabling documented with reasons
- Lattice alias exploit vector comprehensively documented
- One-line closer Set lemmas addressed
- Composition lemmas disabled in function worlds
- `Quotient.eq` disabled in quotient worlds

**Verdict: Strong.**

---

## 9. Example and Counterexample Plan

Every major definition has at least one planned concrete example. The counterexample set is now complete:

| What it disproves | Example | Location |
|-------------------|---------|----------|
| Not reflexive | `≠` on ℕ | W15 L06 |
| Not symmetric | `≤` on ℕ | W15 L04 |
| Not transitive | (specified) | W15 L05 |
| Image preserves intersection | only ⊆ | W07 L05 |
| Injective composition → Injective g | counterexample | W12 L03 |
| InjOn → Injective | counterexample | W13 L03 |
| Overlapping partition | `{{1,2}, {2,3}, {4}}` | W19 L03 |
| Empty-part partition | `{{1,2}, ∅, {3}}` | W19 L04 |
| Function can always be lifted | well-definedness failure | W17 L03 |

**Verdict: Complete.**

---

## Defects

### P0 (blocking)

None.

### P1 (high)

None. All P1 defects from round 1 have been fixed.

### P2 (medium)

1. **`Setoid.quotientKerEquivRange` released in W17 inventory, but `≃` not taught until W22.** The definition/theorem release table (Section 6) lists `Setoid.quotientKerEquivRange` in W17. This theorem produces a result of type `Quotient (ker f) ≃ ↑(Set.range f)`. While no W17 level requires the learner to use it, it will appear in the learner's theorem inventory displaying `≃` notation before they understand what `Equiv` is. This is a minor confusion vector.

   **Fix**: Move `Setoid.quotientKerEquivRange` from the W17 inventory row to W28 (where it's actually used in L01), or hide it until W22.

2. **Coverage closure table overstates R/T for "Binary relation as `Set (α × α)`".** The table claims R=W18 and T=W18 for this item. However, none of the W18 level sketches (same-parity equivalence, same-last-digit setoid, lift through parity quotient, injective kernel, ℤ construction) exercise the `Set (α × α)` representation specifically. The introduction and supported practice in W15 L07–L08 are genuine, but the retrieval and transfer claims are not backed by level content. The W15 boss also uses the `α → α → Prop` form, not `Set (α × α)`.

   **Fix**: Either (a) add a W18 level that requires working with a relation as `Set (α × α)`, or (b) correct the closure table to show R=—, G=—, T=— for this representation and acknowledge it as a supported item (introduced and practiced but not drilled to mastery).

3. **W04 center of gravity remains mixed.** The rationale is provided and defensible, but the grouping of indexed operations with products, nonemptiness, and powerset still introduces 6 concepts across 8 levels. This is the highest concept density of any world in the plan. The rationale argues splitting would create worlds too small, but W23 (PartialEquivWorld) has only 4 levels and works fine.

   **Fix**: This is a judgment call that the architect has already made with rationale. No action required unless authoring reveals problems.

---

## Specific Recommendations (ranked)

1. **(P2)** Move `Setoid.quotientKerEquivRange` from the W17 inventory release to W28, where it is actually used. Avoids showing `≃` notation before Equiv is taught.

2. **(P2)** Correct the coverage closure table: the `Set (α × α)` representation has I=W15, S=W15, but R/G/T should either be substantiated with specific level content in W18 or marked as absent for this specific representation (while the broader "binary relation" item retains its coverage through the `α → α → Prop` form).

3. **(P2, optional)** Consider adding one W18 level that retrieves the `Set (α × α)` representation on a fresh example, to make the closure claim real. This would be a ~1 level addition.

---

## Red Flag Check

| Red flag | Status |
|----------|--------|
| Boss depends on untaught micro-skill | **Clear** |
| World mixes unrelated theorem families | **W04 flagged** — documented with rationale, not blocking |
| Missing docs for newly unlocked inventory | **Clear** |
| Hints don't match failure states | **N/A** — plan stage |
| Psets merely clone lecture examples | **Clear** — psets use fresh surface forms |
| Level introduces too many new burdens | **Clear** |
| Major definition never exercised on concrete example | **Clear** |
| Unresolved local-run or publish breakage | **N/A** — plan stage |

No red flags triggered.

---

## Overall Verdict: **PASS**

All P1 defects from round 1 have been addressed. The plan's architecture is sound: 28 worlds across 8 phases with complete pset pairing, an explicit and complete proof-move coverage table, a substantive transfer plan, thorough inventory release and exploit gating, and comprehensive example/counterexample coverage.

Remaining P2 issues are minor:
- An inventory release timing issue for one theorem (`quotientKerEquivRange` in W17 vs W28)
- An overstated closure claim for one representation (`Set (α × α)` retrieval/transfer)
- A previously-flagged diffuse center in W04 that has been documented with rationale

None of these are structural problems. The plan is ready for world authoring.
