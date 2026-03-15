# W23 MatrixWorld -- Playtest Audit (Round 1)

## 1. Overall verdict

**CONDITIONAL PASS.** The world compiles, has coherent prose, consistent DisabledTactic, and a well-structured progression from L01 through L08. The boss integrates mul_apply, sum_univ_two, ext, fin_cases, transpose_apply, and norm_num. However, there are several P1-P2 issues: `norm_num` with library lemma arguments can collapse the intended multi-step workflow on several levels, `diagonal` is entirely absent from the boss, and L01-L02 risk being overfine (both are `rfl`-only levels with no proof-move teaching). These are fixable without restructuring.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `Matrix.diagonal` is taught in L04 but never retrieved -- absent from the boss. `Matrix.of` is a plan-specified M33 item that is missing entirely (flagged by enrichment). No matrix addition, no identity matrix exercise. |
| 2. Granularity fit | 3 | Each level has one dominant lesson. World center of gravity (matrices as functions) is clear and coherent. L01 and L02 are both `rfl`-only which is slightly overfine but defensible given the conceptual progression (definition vs. construction). |
| 3. Proof-move teaching | 3 | The "expand-unfold-compute" three-step pattern (L06-L07-L08) is well-taught. The `ext` + `fin_cases` pattern for matrix equality (L03) is well-introduced. L01-L02 teach no proof moves (just `rfl`). |
| 4. Inventory design | 3 | New items (Matrix, Matrix.diagonal, diagonal_apply, Matrix.transpose, transpose_apply, Matrix.mul_apply, Fin.sum_univ_two) introduced at appropriate points with good docs. TheoremTab "Matrix" is consistent. All DefinitionDoc and TheoremDoc entries are present for new items. |
| 5. Hint design / recoverability | 3 | Hints are layered: strategy hint (visible) then code hint (hidden). All major proof steps have hints. The boss has detailed strategic hints for both parts. Minor gap: no hints for common wrong moves (e.g., trying `rfl` on L03 or trying `norm_num` directly on L06 without `rw` first). |
| 6. Worked example -> practice -> boss | 3 | Clear progression: L01-L02 (first contact), L03 (ext pattern), L04-L05 (practice), L06-L07 (new technique + practice), L08 (boss). But diagonal is not integrated into the boss, so L04 is an orphan. |
| 7. Mathematical authenticity | 3 | Good "in plain language" sections in every conclusion. Transfer moments present. The matrix-as-function insight is well-communicated. Missing: motivation for *why* matrix multiplication uses sums (enrichment #4). Missing: non-commutativity misconception (enrichment #10). |
| 8. Paper-proof transfer | 3 | Every conclusion connects the Lean proof to ordinary mathematics. L08's conclusion explicitly shows the hand computation mirroring the Lean proof. Good. |
| 9. Technical fit / maintainability | 3 | Compiles cleanly. DisabledTactic consistent across all 8 levels. Dependencies in Game.lean are correct. No import issues. |

**Average: 2.89.** Just below the 3.0 threshold due to the coverage closure score. The world needs the enrichment reviewer's suggestions for `diagonal` in the boss (enrichment #5) and the missing coverage items before it passes the rubric.

---

## 3. Coverage gaps

### 3a. Proof-move layer

| Gap | Severity | Notes |
|-----|----------|-------|
| `diagonal_apply` never retrieved after L04 | HIGH | L04 teaches `rw [Matrix.diagonal_apply]` + `norm_num`. This move is never used again, not even in the boss. L04 is an orphan. |
| No "combine transpose with diagonal" move | MEDIUM | The natural integration of L04 + L05 (e.g., proving `(diagonal d).transpose = diagonal d` for concrete `d`) never appears. |
| No multi-operation move | MEDIUM | No level requires the learner to combine more than two operations in sequence (e.g., transpose of a product, or diagonal times a matrix). The boss comes closest with constructor + ext + mul_apply + sum_univ_two + transpose_apply but the two parts are independent. |

### 3b. Example layer

| Gap | Severity | Notes |
|-----|----------|-------|
| No identity matrix computation | MEDIUM | Mentioned in L04 conclusion but never exercised. The identity is the most important special matrix. (Enrichment #2) |
| No non-commutativity counterexample | MEDIUM | The matrices in L07 give `(AB)_{00} = 19` vs `(BA)_{00} = 23`. This would be a high-value misconception check. (Enrichment #10) |
| No matrix addition example | MEDIUM | The simplest operation on the function representation. (Enrichment #3) |

### 3c. Misconception layer

| Gap | Severity | Notes |
|-----|----------|-------|
| "Matrix multiplication is commutative" | MEDIUM | Never addressed. This is the #1 misconception about matrices. |

---

## 4. Granularity defects

### 4a. Overfine levels

| Pair | Assessment |
|------|-----------|
| L01 + L02 | Both are `rfl`-only levels. L01 proves type equality by `rfl`. L02 proves entry evaluation by `rfl`. The conceptual distinction (definition vs. construction) is real, but two consecutive `rfl`-only levels may feel insubstantial. **Verdict**: P2 (low) -- defensible given the pedagogical framing, but could be merged if other levels are added. |

### 4b. Overbroad levels: None detected

Each level isolates one dominant lesson. The boss is two-part (conjunction) but both parts are manageable.

### 4c. World center of gravity

Stable. "Matrices as functions over finite types" is coherent and all 8 levels stay on-topic.

### 4d. Boss design

The boss integrates mul_apply + sum_univ_two + ext + fin_cases + transpose_apply + norm_num. This is 6 distinct skills. Part 2 (transpose of a product entry) is a novel combination not seen in any prior level. **Not a gauntlet** -- the transpose-of-product integration is genuinely novel.

**However**: `Matrix.diagonal` / `diagonal_apply` from L04 is absent. This makes the boss a partial integrator. See enrichment #5.

---

## 5. Statement exploitability

### Level-by-level analysis

| Level | Can bypass intended lesson? | Severity | Notes |
|-------|---------------------------|----------|-------|
| L01 | No | -- | `rfl` IS the intended proof. No other reasonable path. `norm_num` and `omega` do not close type equalities. |
| L02 | No | -- | `rfl` IS the intended proof. `norm_num` also works but teaches the same lesson (evaluation is definitional). |
| L03 | Unlikely | P2 | `norm_num [Matrix.ext_iff, Fin.forall_fin_two]` might close this in one shot, but it requires knowing `Matrix.ext_iff` and `Fin.forall_fin_two` -- library-level knowledge the learner would not have. Low risk. |
| L04 | P2 exploit via `norm_num [Matrix.diagonal_apply]` | P2 | The intended proof is `rw [Matrix.diagonal_apply]; norm_num`. A learner could write `constructor <;> norm_num [Matrix.diagonal_apply]` as a one-liner. This skips the `rw` step but still requires knowing the lemma name. Not blocking since the lesson is about the lemma itself. |
| L05 | P2 exploit via `norm_num [Matrix.transpose_apply]` | P2 | Same as L04. The learner must still know `transpose_apply`. The `rw` step is pedagogically important but the bypass still requires the correct lemma. |
| L06 | No | -- | After `rw [Matrix.mul_apply, Fin.sum_univ_two]` the goal is definitionally true (`rfl` closes it). No bypass that avoids learning the lemmas. |
| L07 | P1 exploit: `norm_num [Matrix.mul_apply, Fin.sum_univ_two]` | P1 | This one-liner closes the goal without the learner doing the intended three-step pattern (rw + rw + norm_num). The learner can pass `norm_num` the library lemmas as simp arguments, collapsing three steps into one. This bypasses the "expand, then unfold, then compute" workflow that is the dominant lesson. |
| L08 | P1 exploit on Part 2 | P1 | Part 2 can be closed by `norm_num [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]`. Part 1 still requires `ext i j` (matrix equality cannot be closed by `norm_num` alone), so the bypass is partial. But Part 2's integration of transpose + multiplication can be collapsed to a single `norm_num`. |

### Summary

- **P0 exploits**: None. `simp` is correctly disabled. `decide`/`native_decide`/`trivial` are correctly disabled.
- **P1 exploits**: L07 and L08 Part 2 can be one-shot by `norm_num [library_lemmas]`. This bypasses the intended multi-step workflow but requires the learner to know the lemma names. Whether this is a genuine bypass or a "power user shortcut" is debatable -- but the dominant lesson of L07 is the *three-step pattern*, and `norm_num` with arguments collapses it.
- **P2 exploits**: L04, L05 have minor bypass via `norm_num [lemma]` but the bypass still requires knowing the lemma name.

### Recommendations

For **L07**: Consider adding `norm_num` to `DisabledTactic` (or adding a `DisabledTactic norm_num` just for L07) to force the three-step workflow. Then re-enable it for L08 where it is needed as the final step. Alternatively, accept this as a P1 and document it -- a learner who knows to pass library lemmas to `norm_num` is arguably demonstrating understanding.

For **L08**: The Part 1 exploit is blocked by `ext`. Part 2 is exploitable but represents genuine integration (the learner must identify all three lemmas). Accept as P1.

---

## 6. Interactive proof quality

| Level | Red flags | Notes |
|-------|-----------|-------|
| L01 | None | Single `rfl` step. |
| L02 | None | Single `rfl` step. |
| L03 | Minor | `fin_cases i <;> fin_cases j <;> rfl` is a one-liner but each piece is simple. The `<;>` combinator applies uniformly. Acceptable. |
| L04 | None | `constructor` then `rw [diagonal_apply]; norm_num` in each branch. Clear intermediate states. |
| L05 | None | Same pattern as L04. |
| L06 | None | Two sequential `rw` steps with visible goal changes. Excellent interactive quality. |
| L07 | None | Three-step pattern: rw, rw, norm_num. Each step visibly changes the goal. |
| L08 | Minor | The hidden hint shows a multi-line proof. After `ext i j`, the hint suggests `rw [Matrix.mul_apply, Fin.sum_univ_two]` then `fin_cases i <;> fin_cases j <;> norm_num`. The `<;>` chain is long but each component is a taught move. Acceptable for a boss. |

No P1/P2 interactive quality issues.

---

## 7. Learner simulation

### Attentive novice

**First likely stuck point**: L03 (ext + fin_cases). The learner must figure out that matrix equality requires `ext` and that `Fin 2` goals need `fin_cases`. If they have seen `ext` before (it was taught in FinIntro L03 and FinsetOperations L05), they should recognize the pattern. If not, the introduction explains it clearly and the hints provide the exact tactic.

**Most likely wrong move**: Trying `rfl` on L03. The two sides (function definition vs `!!` notation) are not definitionally equal, so `rfl` fails. The learner may be confused after L01-L02 where `rfl` worked. The hint does not explicitly address this wrong move, but the `ext` hint fires at the original goal state, which is appropriate.

**Hints rescue well?** Yes. Every level has a strategy hint and a hidden code hint. The boss has detailed two-part strategy hints.

**Lesson legibility**: Clear. Each level's introduction states the dominant lesson explicitly.

### Experienced Lean user

**Avoidable friction**: L01-L02 may feel trivial (both are `rfl`). An experienced user would dispatch them instantly and learn nothing. However, these levels establish the conceptual foundation and are short enough not to feel burdensome.

**Alias gaps**: None detected. The main proof moves (`ext`, `rw`, `norm_num`, `constructor`, `fin_cases`) are all available.

**Inventory clutter**: Minimal. Only 5 new theorem/definition items across the whole world.

**Needless forced verbosity**: L04-L05 require `rw [diagonal_apply]` + `norm_num` in two branches (for `constructor`). An experienced user might prefer `constructor <;> (rw [...]; norm_num)`. This is supported by the `<;>` combinator. No forced verbosity.

---

## 8. Boss integrity check (L08)

### Seeded subskills

| Subskill | Seeded? | Where |
|----------|---------|-------|
| `ext i j` for matrix equality | Yes | L03 |
| `fin_cases i <;> fin_cases j` | Yes | L03 |
| `rw [Matrix.mul_apply]` | Yes | L06 |
| `rw [Fin.sum_univ_two]` | Yes | L06 |
| `norm_num` for arithmetic | Yes | L04, L07 |
| `rw [Matrix.transpose_apply]` | Yes | L05 |
| `constructor` | Yes | L04, L05 |
| `rw [Matrix.diagonal_apply]` | **NO** | L04 teaches it but boss does not use it |

### Closure quality

Mostly good. All subskills used in the boss have been introduced (I), practiced (S), and are now integrated (G). The exception is `diagonal_apply`, which reaches only (I) + (S) in L04 and is never revisited.

### Integration quality

Part 1 requires: constructor + ext + mul_apply + sum_univ_two + fin_cases + norm_num (6 skills).
Part 2 requires: constructor + transpose_apply + mul_apply + sum_univ_two + norm_num (5 skills).

The parts are independent (joined by `constructor`). Part 2 is a novel combination: the learner has never combined transpose with multiplication before. This is genuine integration, not just concatenation.

### Surprise burden

None. Every move in the boss was taught in L03-L07. The proof length is comparable to the practice levels. No new concepts.

### Can the learner explain in words why the proof works?

Yes. "To show A^2 = B, I checked every entry: expand the product, unfold the sum, compute. To show the transpose entry is zero, I swapped indices, expanded, and computed." The conclusion's transfer section confirms this.

### Verdict

**Not a gauntlet, not a lottery.** The boss is a legitimate integration level. Its only weakness is the absence of `diagonal_apply`.

---

## 9. Course-role sanity

| Level | Intended role | Actual role | Match? |
|-------|--------------|-------------|--------|
| L01 | First contact: Matrix definition | First contact | Yes |
| L02 | First contact: Matrix construction | First contact | Yes |
| L03 | First contact + practice: ext for matrices | Practice (ext was taught before; this is a new application) | Yes |
| L04 | First contact: Matrix.diagonal | First contact | Yes |
| L05 | First contact: Matrix.transpose | First contact | Yes |
| L06 | First contact: Matrix.mul_apply | First contact | Yes |
| L07 | Practice: concrete multiplication | Practice | Yes |
| L08 | Boss | Boss | Yes |

All roles match. No level is miscast.

---

## 10. Technical risks

| Risk | Severity | Notes |
|------|----------|-------|
| Build succeeds | -- | `lake build` passes with 8380 jobs. Only warnings, no errors. No MatrixWorld-specific warnings. |
| Missing `TacticDoc` | None | All disabled tactics have TacticDoc entries from earlier worlds. |
| Missing `TheoremDoc` / `DefinitionDoc` | None | All new items have documentation. |
| `omega` not disabled | P2 | `omega` is not in DisabledTactic. For the concrete arithmetic in L04, L07, L08, `omega` might close goals after `rw`. Not a serious concern since the intended proof already uses `norm_num` for arithmetic and `omega` would be a reasonable alternative. |
| No `NewTactic` declarations in any level | INFO | All tactics used (ext, fin_cases, norm_num, constructor) were introduced in earlier worlds. This is correct behavior -- no need to redeclare. However, `ext` applied to matrices is a conceptually new use; a `NewTactic` reminder could help (enrichment #8). |

---

## 11. Ranked patch list

### P1 (High priority)

1. **L07: `norm_num [Matrix.mul_apply, Fin.sum_univ_two]` one-shot bypass.** The intended three-step pattern is the dominant lesson, and passing library lemmas to `norm_num` collapses it. Fix: either (a) add `norm_num` to `DisabledTactic` for L07 only (replace the `norm_num` step with `ring` or explicit arithmetic rewrites), or (b) accept as P1 and document. Option (b) is more pragmatic since the learner must still identify the correct lemma names.

2. **L08 Part 2: same `norm_num` bypass.** Fix: same options as #1. Since Part 1 requires `ext` (no bypass), the boss is only partially exploitable. Accept as P1.

3. **Boss coverage gap: `diagonal_apply` absent from boss.** L04 is orphaned. Fix: add a Part 3 to the boss conjunction involving a diagonal matrix entry, e.g., `Matrix.diagonal (fun i : Fin 2 => (i.val + 1 : Int)) 1 1 = 2`. This is low effort and closes the coverage gap. (Also flagged by enrichment #5.)

### P2 (Medium priority)

4. **L04/L05 minor bypass via `norm_num [lemma]`.** The bypass requires knowing the lemma name, so the learner is still engaging with the right API. Accept as P2.

5. **No wrong-move hints for L03.** A learner trying `rfl` on L03 gets a Lean error but no game hint. Consider adding a `Hint (hidden := true) "If you tried `rfl`, it does not work here because the two sides use different representations. Use `ext i j` to reduce to entry-wise equality."` at the initial goal state, triggered when the learner is stuck.

6. **L01-L02 both `rfl`-only.** Two consecutive levels with identical proof technique. Not blocking (the conceptual content differs) but could feel insubstantial. Consider enriching L02 to verify two entries (not just one) to give it more substance.

### INFO (Low priority)

7. **Enrichment suggestions #1-#5 (Matrix.of, identity matrix, matrix addition, multiplication motivation, boss diagonal integration)** are all coverage improvements. The audit confirms the enrichment reviewer's findings. Implement all "Yes" recommendations from the enrichment review.

8. **Enrichment #10 (non-commutativity misconception)** is a high-value addition. A remark in L07's conclusion showing that `(B * A) 0 0 = 23 != 19 = (A * B) 0 0` would cost one sentence and address a major misconception.

---

## 12. What to playtest again after patching

After implementing the enrichment suggestions and the patches above:

1. **Re-audit the boss** -- if a diagonal component is added (patch #3), verify that the boss still integrates properly and does not become a gauntlet (concatenation of independent parts).
2. **Re-check exploitability** -- if `norm_num` is disabled on L07, verify that the intended proof still works (it should -- the proof uses `rw` first, then `norm_num`). Also verify that no new exploits are introduced by any added levels.
3. **Re-simulate for the novice** -- if new levels are added (Matrix.of, identity, addition, non-commutativity), check that the novice path remains smooth and the novelty budget is respected (one new burden per level).
4. **Verify DisabledTactic consistency** -- all new/modified levels must have the standard disabled set.
