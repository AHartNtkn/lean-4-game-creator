# Playtest Audit: PsetCounting

**World**: PsetCounting (8 levels, L01-L08)
**Type**: Problem Set for CountingTechniques (W27)
**Auditor**: Phase 2d playtest
**Date**: 2026-03-23

---

## 1. Overall Verdict: PASS

The world is a well-crafted pset that retrieves and transfers all four counting techniques from CountingTechniques. Each level has a clear dominant lesson, the boss integrates 5+ moves, all subskills are seeded, and the difficulty progression is appropriate. No P0 defects found.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | All 4 techniques covered; minor gap on `le_antisymm` retrieval |
| Granularity fit | 4 | Each level is well-scoped; progression L01-L08 is natural |
| Proof-move teaching | 3 | Good retrieval testing; L05 is near-clone of CT L17 |
| Inventory design | 3 | No new items (correct for pset); disabled theorems well-chosen |
| Hint design and recoverability | 3 | Strategy hints visible, code hidden; one hint gap in L04 |
| Worked example -> practice -> transfer -> boss | 3 | Good mix of retrieval (L01-L05) and transfer (L06-L07); boss integrates well |
| Mathematical authenticity | 4 | Real-world framing (league divisions, categories); clear technique identification in conclusions |
| Paper-proof transfer | 3 | Conclusions connect Lean moves to paper mathematics; boss conclusion has excellent proof-chain table |
| Technical fit and maintainability | 3 | Compiles cleanly (warnings only); minor TheoremDoc warnings on disabled theorems |

**Average**: 3.22
**Minimum**: 3

---

## 3. Summary Statistics

- 8 levels (6 planned, 2 additional practice levels added)
- Average rubric score: 3.22 / 4.0
- Minimum rubric score: 3 / 4.0
- P0 defects: 0
- P1 defects: 0
- P2 defects: 4

---

## 4. P0 Defects

None.

---

## 5. P1 Defects

None.

---

## 6. P2 Defects

### P2-1: L05 near-clones CT L17 (generalized pigeonhole)

**Level**: L05_CategorySizes
**Issue**: The proof structure is identical to CountingTechniques L17: `by_contra` + `push_neg` + `hmem` boilerplate + `card_eq_sum_card_fiberwise` + `sum_le_sum` + `sum_const/smul_eq_mul` + `omega`. The only difference is concrete numbers (10 items, 3 categories, threshold 3) vs generic parameters (n items, m bins, threshold k).
**Why it matters**: Psets should test transfer to fresh surface forms, not just retrieval with different constants.
**Mitigation**: The world HAS genuine transfer elsewhere (L06 indirect bound, L07 chained bounds). L05 serves as unsupported retrieval, which is a legitimate pset function. The level is self-aware: the conclusion says "This is the counting contradiction pattern from CountingTechniques L16."
**Recommendation**: Acceptable as-is. If revised, consider a problem where the contradiction setup is less obvious — e.g., the learner must first establish a cardinality fact before the averaging argument applies.

### P2-2: L04 missing hint before `rw [h]`

**Level**: L04_LeagueDivisions
**Issue**: After `rw [Finset.card_univ, Fintype.card_fin] at h`, the learner has `h : n = ∑ ...` and goal `n = 32`. No hint fires here. The next hint fires only after `rw [h]` changes the goal to `∑ ... = 32`.
**Why it matters**: A stuck learner has no rescue at this point.
**Mitigation**: `rw [h]` when you have `h : n = expr` and goal `n = 32` is a basic move taught in early worlds. For a pset with reduced scaffolding, this gap is expected.
**Recommendation**: Could add a hidden hint: "You have `h : n = ∑ ...`. Rewrite the goal with `rw [h]`." Low priority.

### P2-3: Multi-rewrite chains in hints

**Levels**: L04, L05, L08
**Issue**: Hints suggest long rewrite chains like `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. The learner must type the entire chain correctly before feedback.
**Why it matters**: Interactive-hostile — no intermediate feedback if one rewrite name is wrong.
**Mitigation**: Each individual rewrite would also work (the learner CAN do them one at a time). The chain form is shown because it's standard practice. These rewrites were practiced in CT L12-L17.
**Recommendation**: No change needed. The chain pattern was well-practiced in the lecture world.

### P2-4: Missing TheoremDoc for disabled theorems in L08

**Level**: L08_Boss
**Issue**: Build log shows "Missing Theorem Documentation: Fintype.card_of_bijective" and "Missing Theorem Documentation: Fintype.card_congr" for `DisabledTheorem` entries. These are cosmetic warnings since the theorems are disabled and not player-facing.
**Recommendation**: Add minimal `TheoremDoc` entries before the `DisabledTheorem` line, or accept the warnings.

---

## 7. Coverage Gaps

### Minor: `le_antisymm` (sandwich equality) not retrieved

`le_antisymm` was a key technique in CT L04 and CT L19 (boss). In PsetCounting, L03 uses `omega` instead of explicit `le_antisymm` to combine two opposing bounds. The specific move of "two bounds -> le_antisymm -> equality" is never explicitly tested.

**Assessment**: `omega` handles this automatically and is more practical. The mathematical reasoning (two opposing bounds imply equality) is the same. Not blocking.

### Minor: Equiv construction not tested

The PLAN says L01 should "construct an Equiv and conclude equal cardinality." The implementation gives the Equiv as a hypothesis. However, CT L01 also gives the Equiv, so this is consistent across lecture and pset.

**Assessment**: Constructing an Equiv from scratch is a significant programming task that may be out of scope. Not blocking.

---

## 8. Granularity Defects

None. The 8-level structure is well-paced:
- L01-L03: Single-technique retrieval (bijection, pigeonhole, bounds)
- L04-L05: Double counting retrieval (uniform fibers, contradiction+fibers)
- L06-L07: Multi-technique transfer (indirect bound, information chaining)
- L08: Boss integration

---

## 9. Learner Simulation Notes

### Attentive Novice

- **L01**: Should succeed. `card_congr` + `card_fin` is a 3-step pattern practiced in CT L01.
- **L02**: The `obtain ⟨a, b, hne, heq⟩` destructuring is the main challenge. Hidden hint gives full syntax. `intro hinj; exact hne (hinj heq)` requires understanding of how injectivity creates a contradiction with `hne`. Good reasoning demand.
- **L04**: The `hmem` boilerplate is the main friction point. Hint provides it. The `rw [h]` step after establishing h has no hint — novice must recognize this basic move independently. Appropriate for pset.
- **L05**: Hardest non-boss level. Requires recognizing `by_contra` as opening strategy. First visible hint ("What if nothing satisfies it?") guides well. The 8-step proof is within practiced range (CT L16 has same structure).
- **L07**: Must recognize that injection bound on `f` constrains `card α`, enabling pigeonhole on `g`. First visible hint ("One function constrains a type's size") provides good guidance. Key insight is which function to apply which theorem to.
- **L08 Boss**: 9 steps, all previously practiced. The novel integration is using injection bound on `f` to feed the fiber contradiction on `g`. Hint at each step. Should be achievable with hints.

### Experienced Lean User

- L01 is trivially easy (2 rewrites + exact).
- `hmem` boilerplate is repetitive but unavoidable.
- L06 (composition + surjection) and L07 (information chaining) are the most interesting levels — non-obvious technique selection.
- No alias gaps or inventory clutter issues.

---

## 10. Pset Integrity Notes

### Fresh surface form check
- L01: Fin m ≃ Fin n (vs abstract α ≃ β in CT L01) — mild surface change
- L02: `¬ Function.Injective f` from witnesses (vs CT L09's direct `apply`) — structural change, good
- L03: Combined surjection + injection (not in CT as single level) — fresh combination
- L04: League divisions with Fin/Fintype (vs CT L12's abstract Finset) — surface change
- L05: Categories with concrete numbers (vs CT L17's generic parameters) — near-clone (see P2-1)
- L06: Composition + surjection (genuinely new problem shape) — strong transfer
- L07: Two-function chaining (genuinely new problem shape) — strong transfer
- L08 Boss: Injection feeds fiber contradiction (new combination) — strong integration

### Reduced scaffolding check
- All code hints are hidden. ✓
- Strategy hints are visible in L02, L05, L07, L08. ✓
- No step-by-step walkthroughs in introductions. ✓

### Real retrieval check
- Learner must select which counting technique applies (not told). ✓
- L06 and L07 require technique selection that's non-obvious from the hypotheses. ✓

---

## 11. Technical Risks

1. **Build warnings**: Missing TheoremDoc warnings for disabled theorems in L08. Cosmetic only.
2. **Multi-rewrite chain fragility**: Long `rw` chains depend on exact Lean/Mathlib API names. A Mathlib update renaming `smul_eq_mul` or `Finset.sum_const` would break multiple levels.
3. **`hmem` boilerplate**: The `fun _ _ => Finset.mem_univ _` pattern appears in 3 levels (L04, L05, L08). If the `card_eq_sum_card_fiberwise` API changes, all three break.

---

## 12. Ranked Patch List

1. **(P2-2) Add hidden hint in L04 before `rw [h]`**: Between the `rw [...] at h` and `rw [h]` steps, add a hidden hint: "You have `h : n = ∑ ...`. Try `rw [h]`." — 2 minutes, improves rescue path.

2. **(P2-4) Add TheoremDoc for disabled theorems in L08**: Add minimal doc entries for `Fintype.card_of_bijective` and `Fintype.card_congr` before their `DisabledTheorem` line to silence build warnings. — 5 minutes.

3. **(P2-1) Consider freshening L05**: If revising, make the counting contradiction less templated — e.g., require an intermediate cardinality computation before the averaging argument applies. — 30 minutes.

4. **(P2-3) No action needed**: Multi-rewrite chains are standard and well-practiced.

---

## 13. What to Playtest Again After Patching

- If P2-2 is applied: Verify L04 hint fires at the correct goal state.
- If P2-4 is applied: Verify clean build with no TheoremDoc warnings for PsetCounting levels.
- If L05 is revised: Full playtest of L05 including hint coverage and exploitability check.
