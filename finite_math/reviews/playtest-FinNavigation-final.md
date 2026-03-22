# Playtest Audit: finite_math

**Worlds audited**: MeetFin (21 levels), FinNavigation (10 levels)
**Worlds listed but not yet authored**: 27 of 29 (FinTuples through Finale do not exist yet)
**Date**: 2026-03-20

---

## 1. Overall Verdict: PASS

Both authored worlds are solid. No P0 defects found. The pedagogy is well-sequenced, hints are layered correctly, exploits are blocked where needed, and both bosses test genuine integration of taught skills. The worlds form a strong foundation for Phase 1 of the course.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Good coverage of Fin basics. `.isLt` pattern is slightly undermined by omega's Fin-awareness (P2). Transfer stage deferred to unbuilt PsetFin. |
| Granularity fit | 4 | Each level isolates one dominant lesson. 21 levels in MeetFin is large but justified — each level has a distinct purpose. FinNavigation's 10 levels are well-calibrated. |
| Proof-move teaching | 4 | Proofs are broken into named, reusable patterns ("Fin equality pattern", "Fin contradiction pattern", "rewrite-to-values"). Conclusions explicitly name and tabulate the patterns. |
| Inventory design | 4 | Items unlocked at the right time. Docs are thorough for every new item. Disabled tactics/theorems are precisely targeted. `Fin.forall_fin_two`, `Unique.eq_default`, `Subsingleton.elim`, `Fin.castSucc_inj`, `Fin.succ_inj` all correctly blocked. |
| Hint design and recoverability | 3 | Layered hints (strategy visible, code hidden) throughout. Rescue paths exist at every step. Minor: some boss hints are very specific (nearly giving the full answer), which is appropriate for deeply nested case analysis but reduces the discovery element. |
| Worked example -> practice -> transfer -> boss | 3 | Good progression within each world. MeetFin moves from demonstration (L01-L04) to practice (L05-L10) to new territory (L11-L20) to boss (L21). Transfer stage is deferred to the unbuilt PsetFin world. |
| Mathematical authenticity | 4 | Introductions connect Lean concepts to standard math. Boundary cases (Fin 0, Fin 1) are concretized. The decomposition theorem is presented as a structural insight, not just a proof exercise. Conclusions explain "why this matters." |
| Paper-proof transfer | 4 | Conclusions consistently connect Lean moves to plain-math reasoning. Tables like "Move / Tool / Learned in" in the MeetFin boss help the learner organize their knowledge. The decomposition is linked to "$k \leq n$ implies $k < n$ or $k = n$." |
| Technical fit and maintainability | 3 | Builds cleanly (warnings only, no errors). Metadata.lean has complete docs. `Fin.val_injective` is not disabled, which allows a minor bypass of L05's intended approach (P2). |

**Average score**: 3.56
**Minimum score**: 3

---

## 3. Summary Statistics

- Average: 3.56
- Minimum: 3 (Coverage closure, Hint design, Worked example progression, Technical fit)
- No category below 2
- No automatic red flags triggered

---

## 4. P0 Defects (Blocking)

None.

---

## 5. P1 Defects (High Priority)

None.

---

## 6. P2 Defects (Medium)

### P2-1: `omega` bypasses `.isLt` extraction in MeetFin L03 and L11

**Observed**: After `intro x`, `omega` alone closes the goal `x.val ≠ 5` (L03) and `x.val ≤ n` (L11) without the learner ever extracting `.isLt`. Tested and confirmed: `omega` automatically sees Fin bounds on `.val` goals.

**Impact**: The dominant lesson ("extract the bound with `have h := x.isLt`") is bypassable. However, the `.isLt` pattern is NOT bypassable for L12 (`Fin 0 → False`) — omega alone fails there. So the pattern is taught when it's truly needed.

**Mitigating factors**: Hints guide the intended approach. Conclusions explain the pattern. The bypass only helps on goals involving `.val` — it doesn't work for deriving `False` or goals involving `Fin.last`/`castSucc`.

**Recommendation**: No change needed. The levels work as designed for hint-following learners. An experienced user who types `omega` directly still reads the explanation.

### P2-2: `Fin.val_injective` and `Fin.ext` (lemma form) not disabled

**Observed**: `exact Fin.ext h` or `exact Fin.val_injective h` one-shots MeetFin L05, bypassing the `rw [Fin.ext_iff]` rewrite that the level teaches.

**Impact**: Low. `Fin.ext h` is essentially the same insight as `rw [Fin.ext_iff]; exact h` — the learner still understands that value equality implies element equality. The rewrite form is more general (works with the goal, not just hypotheses), so the lesson is still valuable.

**Recommendation**: No change needed. Both approaches teach the same concept.

### P2-3: `rfl` closes FinNavigation L01, L03, L04

**Observed**: The val lemmas are transparent definitions, so `rfl` works instead of the named lemma. This is explicitly noted in the conclusion text of each level.

**Impact**: Low. The conclusions explain that named lemmas are needed when `n` is a variable (which it is in the boss). `rfl` only works for concrete `n`.

**Recommendation**: No change needed. The author correctly handles this.

---

## 7. Coverage Gaps

### Within the two authored worlds

No gaps. Both worlds cover their planned scope from the coverage map:

**MeetFin covers**:
- `Fin n` type, construction, extraction (I, S stages)
- `Fin.val`, coercion `↑i` (I, S stages)
- `Fin.ext_iff` / `ext` (I, S, R stages)
- `Fin 0` empty, `Fin 1` singleton, `Fin 2` case analysis (I, S, R, W stages)
- Destructuring with `cases` (I, S stages)
- Existential witnesses with Fin (I stage)
- Inequality proving for Fin (I stage)

**FinNavigation covers**:
- `Fin.last`, `Fin.castSucc`, `Fin.succ` (I, S, R stages)
- Val lemmas and rewrite-to-values strategy (I, S, R stages)
- Separation fact (castSucc ≠ last) (I, S stages)
- castSucc injectivity (I stage)
- last-or-castSucc decomposition (I, G stages)

### Between authored and unbuilt worlds

- Transfer (T) stage for all items deferred to PsetFin (not yet authored)
- Generalization to variable `n` partially done (MeetFin L11, FinNavigation boss) but full generalization awaits later worlds
- FinTuples (`Fin.cons`, `Fin.snoc`, function extensionality) not yet authored
- All Finset, Fintype, big-operator, and combinatorics content not yet authored

---

## 8. Granularity Defects

None. Both worlds have stable centers of gravity:

- **MeetFin**: "Construct, extract, compare, and case-analyze elements of Fin n"
- **FinNavigation**: "Navigate Fin n using last, castSucc, and succ; prove the last-or-castSucc decomposition"

No world mixes unrelated theorem families. Level scoping is tight — each level has one dominant lesson.

MeetFin at 21 levels is large but not bloated: the equality section (L05-L10) teaches 6 distinct skills (ext_iff forward, ext_iff backward, rw at hypothesis with ext_iff, rw hypothesis at hypothesis, round-trip eta, proof irrelevance). The boundary-case section (L12-L14) covers three genuinely different scenarios (empty → False, empty → anything, singleton). The case-analysis section (L15-L17) builds from destructuring to Fin 2 to Fin 3.

---

## 9. Learner Simulation Notes

### Attentive novice

**First stuck point**: MeetFin L05 (first use of `Fin.ext_iff`). The introduction explains the concept clearly and the hint gives the exact syntax. Recovery: smooth.

**Most likely wrong move on L16**: Trying `left; rfl` before destructuring `x`. The hint fires and redirects to `cases x with | mk v hlt =>`. Recovery: good.

**MeetFin Boss (L21) Part 2**: This is the hardest challenge. The learner must combine case analysis (L15-L17) with existential witnesses (L20) and inequality proving (L19) across 3 valid cases + 1 impossible case. The hints provide step-by-step guidance at every branch. A novice who reads hints will complete it, but it will feel like the longest proof they've done. Expected completion: 10-15 minutes for Part 2 alone.

**FinNavigation Boss (L10) Part 1**: Requires deciding whether each case represents `last` or a `castSucc` preimage. This decision was never practiced together before — L08 and L09 teach the patterns individually. Hints guide the decision at each branch. The novice will need hints on the first case but may recognize the pattern by the second case.

**Hint rescue quality**: Good throughout. Layered hints (strategy first, code second) match the failure states. No dead-end states were found where a learner could be stuck with no applicable hint.

### Experienced Lean user

**MeetFin**: Will type `omega` on L03 and L11 without extracting `.isLt`, getting a shorter proof than intended. Will use `ext; omega` or `Fin.ext h` as one-liners on equality goals. The 21-level count will feel long — an experienced user could absorb the content in ~10 levels. However, the extra levels provide valuable practice reps that the novice needs.

**FinNavigation**: Will find L01-L04 very straightforward (exact + named lemma or rfl). The world picks up difficulty at L05 (combining val lemmas) and L06 (separation fact). The boss is satisfying even for experienced users — the decomposition proof has enough structure to feel like real mathematics.

**Avoidable friction**: None found. The inventory is clean, no clutter, no unnecessary items.

---

## 10. Boss Integrity Notes

### MeetFin Boss (L21)

**Subskill inventory** (all taught before the boss):
| Subskill | Taught in |
|----------|-----------|
| `constructor` | L01 (NNG4 baseline) |
| `ext` | L14 |
| `rw [Fin.ext_iff] at h` | L07 |
| `omega` | L01 |
| `cases x with \| mk v hv =>` | L15 |
| Nested `cases v` | L16, L17 |
| `use ⟨k, by omega⟩` | L20 |
| `intro h; cases h` (discrimination) | L19 |
| `absurd hv (by omega)` | L16 |

**Integration moves** (first-time combinations in boss):
- Part 1: `ext` on goal + `Fin.ext_iff at h` on hypothesis + `omega` to chain. Mild integration — each piece is familiar.
- Part 2: `use ⟨k, by omega⟩` + `intro h; cases h` per case. This sequence was never practiced as a unit, but each piece was practiced individually. Appropriate boss-level integration.

**Verdict**: Boss integrates without introducing. All subskills seeded. Proof length (~20 steps) is long but manageable with hints.

### FinNavigation Boss (L10)

**Subskill inventory** (all taught before the boss):
| Subskill | Taught in |
|----------|-----------|
| `constructor` | MeetFin L01 |
| Destructure + nested case split | MeetFin L15-L17 |
| `right; use ⟨k, by omega⟩; ext; rw [Fin.val_castSucc]` | L09 |
| `left; ext; rw [Fin.val_last]` | L08 |
| `absurd hv (by omega)` | MeetFin L16 |
| `rw [Fin.ext_iff] at h` + val lemmas at h | L06, L07 |
| `ext; omega` | MeetFin L14 |

**Integration moves**:
- Part 1: Deciding whether a case is "last" (L08) or "castSucc preimage" (L09) based on the value. This decision logic is new, but the world introduction explicitly describes the decomposition. Hints guide each case.
- Part 2: Succ injectivity — straightforward application of the L07 pattern with `val_succ` instead of `val_castSucc`.

**Verdict**: Boss integrates without introducing. The decision logic in Part 1 is the world's central insight, appropriately tested at boss level.

---

## 11. Technical Risks

1. **Translation warnings in build log**: Expected GameServer behavior. Every `TacticDoc`/`TheoremDoc` string triggers a translation warning. Not a real issue.

2. **`Mathlib.Data.Fin.Basic` import**: Provides the full Fin API. Some potentially-exploitable lemmas are available but the ones that matter (`Fin.castSucc_inj`, `Fin.succ_inj`, `Fin.forall_fin_two`, `Unique.eq_default`, `Subsingleton.elim`) are correctly disabled per-level. Lesser lemmas like `Fin.val_injective` are available but not damaging (P2-2 above).

3. **`norm_num` not disabled in MeetFin L01-L17**: Tested — `norm_num` doesn't close any of the Fin-reasoning goals in these levels. The goals involve Fin equality/inequality, not pure arithmetic. `norm_num` is correctly disabled from L18 onward where concrete function values appear.

4. **`tauto` not disabled**: Not a concern — all goals involve Fin-specific reasoning or arithmetic that `tauto` cannot handle.

---

## 12. Ranked Patch List

No mandatory patches. The following are optional improvements, ranked by impact:

1. **(Optional, low priority)** Consider adding a "coaching" level between FinNavigation L09 and L10 that practices the decomposition on a single element (e.g., "Is `⟨1, by omega⟩ : Fin 4` equal to `Fin.last 3`? If not, find its castSucc preimage.") This would smooth the transition to the boss's multi-case integration. However, the boss hints adequately rescue this gap.

2. **(Optional, cosmetic)** MeetFin L09 title "The Round-Trip Property" overlaps with L04 title "Construction and Extraction" which also covers the round-trip concept. Consider renaming L09 to "Identifying Fin Elements" to better distinguish the two levels.

---

## 13. What to Playtest Again After Patching

No patches are required, so no re-playtest is needed for the current two worlds.

When the next worlds are authored (FinTuples, PsetFin), the following should be verified:
- PsetFin uses fresh surface forms (not clones of MeetFin/FinNavigation examples)
- FinTuples properly builds on the last-or-castSucc decomposition from FinNavigation
- PsetFin boss integrates 5+ moves across all three prerequisite worlds
- `funext` introduction in FinTuples is properly scaffolded (this is a new tactic type)

---

## Appendix: Worlds Not Yet Authored (27 of 29)

The following worlds from the plan do not yet exist as files:

**Phase 1 remaining**: FinTuples, PsetFin
**Phase 2**: FinsetBasics, FinsetOperations, FinsetImage, PsetFinset
**Phase 3**: Cardinality, AbstractionLadder, Fintype, CountingTypes, PsetCardinality
**Phase 4**: BigOpIntro, BigOpAlgebra, FinsetInduction, SummationFormulas, PsetBigOp
**Phase 5**: BinomialCoefficients, Powerset, BinomialTheorem, PascalsTriangle, PsetCombinatorics
**Phase 6**: Products, Finsupp, Matrices, CountingTechniques, PsetCounting
**Phase 7**: Finale

These were listed in the audit request but cannot be reviewed because no level files exist for them. This audit covers only the two implemented worlds.
