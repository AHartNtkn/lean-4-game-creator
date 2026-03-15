# W9 FinsetCardinality -- Playtest Audit (Round 1)

## 1. Overall verdict

**FAIL.** The world compiles and has coherent prose, but it is exploitable on nearly every level, the boss is a gauntlet (no integration), and the learner never performs a multi-step cardinality proof. These are structural problems, not polish issues.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `card_insert_of_notMem` chaining pattern described but never exercised; no multi-step computation; disjoint-union case skipped |
| 2. Granularity fit | 3 | Each level has one dominant lesson; world center of gravity is stable |
| 3. Proof-move teaching | 1 | Every level is a single `rw` or `exact`. No proof moves are taught. The world is theorem trivia. |
| 4. Inventory design | 3 | New theorems introduced at appropriate points; retrieval levels (L02, L03) are sensible |
| 5. Hint design / recoverability | 3 | Hints are layered (strategy visible, code hidden); but hints are trivially shallow because the proofs are trivially short |
| 6. Worked example -> practice -> boss | 1 | Boss is a gauntlet of three independent single-lemma applications; no progression from demonstration to independence |
| 7. Mathematical authenticity | 2 | Good prose explaining inclusion-exclusion; but the learner never actually *does* a computation. Numbers in the conclusion text are not forced through the learner's hands. |
| 8. Paper-proof transfer | 3 | Transfer moments are well-placed (L07 additive vs subtractive, L09 conclusion) |
| 9. Technical fit / maintainability | 2 | `simp` not disabled = P0 exploit; `norm_num` not disabled = P1 exploit; missing TacticDoc (info-level, not blocking) |

**Average: 2.2.** Below the 3.0 threshold. Two categories at 1. The world is not "good" by the rubric.

---

## 3. Coverage gaps

### 3a. Proof-move layer gaps

| Gap | Severity | Notes |
|-----|----------|-------|
| Multi-step `card_insert_of_notMem` chaining | HIGH | L03's conclusion describes the "peel off inserts" pattern but no level exercises it. The learner never chains `card_insert_of_notMem` -> `card_insert_of_notMem` -> `card_singleton`. |
| Producing non-membership proofs | HIGH | L03 gives `h : a not in s` as a hypothesis. In real use, the learner must *derive* non-membership (e.g., `by decide` or via `Finset.not_mem_empty`). Never practiced. |
| Combining cardinality lemmas with arithmetic | MEDIUM | No level requires the learner to do arithmetic after rewriting (e.g., `1 + 1 + 1 = 3`). All conclusions are either closed by the lemma itself or are `rfl`. |

### 3b. Example layer gaps

| Gap | Severity | Notes |
|-----|----------|-------|
| Concrete inclusion-exclusion computation | HIGH | L07 applies `card_union_add_card_inter` structurally. The learner never verifies `4 + 2 = 3 + 3` or computes `({1,2,3} cup {2,3,4}).card = 4` by hand. Numbers are in the conclusion text but not in the proof. |
| Disjoint union as special case | MEDIUM | `card_union_of_disjoint` is never shown. The enrichment reviewer (suggestion 1) flagged this correctly. |

### 3c. Misconception layer

| Gap | Severity | Notes |
|-----|----------|-------|
| L06 misconception calibration is good | -- | The range-zero level addresses 0-indexing confusion well. |
| Missing: "card of insert without membership proof" trap | LOW | L04 sets up the contrast but doesn't explain *why* `card_insert_of_notMem` has its hypothesis. Enrichment suggestion 10. |

---

## 4. Granularity defects

### 4a. Overfine levels: None detected
All 9 levels have distinct dominant lessons. No adjacent levels differ only by renaming.

### 4b. Overbroad levels: None detected
Each level isolates one new concept.

### 4c. World center of gravity
The world is centered on `Finset.card` and its lemmas. This is coherent.

### 4d. Missing levels (too shallow)

| Missing level | Why needed |
|---------------|-----------|
| Multi-step cardinality computation (e.g., `({1,2,3} : Finset Nat).card = 3`) | The "peel off inserts" pattern is the core proof technique this world should teach. Currently only described in prose. |
| Disjoint union cardinality | Conceptual prerequisite for understanding why inclusion-exclusion has the `+ (s cap t).card` term. |
| Concrete inclusion-exclusion (compute the number) | Forces the learner to actually combine lemmas rather than applying one lemma. |

---

## 5. Statement exploitability

### P0: `simp` not disabled -- closes 7 of 9 levels

**Tested and confirmed.** `simp` (bare, without arguments) closes:
- L01: `(emptyset : Finset Nat).card = 0` -- `simp`
- L02: `({42} : Finset Nat).card = 1` -- `simp`
- L03: abstract `card_insert_of_notMem` -- `simp [h]` (needs hypothesis, but `simp` with the hypothesis closes it)
- L04: abstract `card_insert_of_mem` -- `simp [h]`
- L05: `(Finset.range 5).card = 5` -- `simp`
- L06: `range 0 = emptyset and card = 0` -- `simp`
- L07: inclusion-exclusion instance -- `simp`

Only L08 (`card_filter_le`) and L09 part 3 resist `simp`.

**Fix**: Add `simp` to `DisabledTactic` on ALL levels. This is the standard disabled set for this course (`trivial decide native_decide simp aesop simp_all`).

### P1: `norm_num` closes 6 of 9 levels

**Tested and confirmed.** `norm_num` closes:
- L01, L02, L05, L06, L07, and L09 parts 1-2.

Only L03, L04 (abstract), L08, and L09 part 3 resist `norm_num`.

**Fix**: Add `norm_num` to `DisabledTactic` on L01, L02, L05, L06, L07, and L09. Alternatively, add it to all levels for consistency.

### P2: `rfl` on concrete cardinality goals

`rfl` closes `(Finset.range 5).card = 5` (L05) and `(emptyset : Finset Nat).card = 0` (L01). This is definitional and cannot be disabled. Accept as P2 (known limitation).

### P2: `decide` is disabled -- good
`decide` would close all concrete goals but is already in `DisabledTactic`. Correct.

---

## 6. Interactive proof quality

### Assessment: POOR

Every level in this world has a 1-step proof. The learner types one tactic and the level is done. There is no interactive exploration cycle -- no "type a step, see how the proof state changed, decide what to do next." This is the antithesis of what lean4game is designed for.

| Level | Proof steps | Interactive quality |
|-------|-------------|-------------------|
| L01 | 1 (`rw [Finset.card_empty]`) | No exploration |
| L02 | 1 (`rw [Finset.card_singleton]`) | No exploration |
| L03 | 1 (`exact ... h`) | No exploration |
| L04 | 1 (`exact ... h`) | No exploration |
| L05 | 1 (`rw [Finset.card_range]`) | No exploration |
| L06 | 3 (`constructor`, `exact`, `rw`) | Minimal exploration |
| L07 | 1 (`exact ... _ _`) | No exploration |
| L08 | 1 (`exact ... _ _`) | No exploration |
| L09 | 5 (`refine`, 3x `exact`) | Lemma selection only |

L06 is the ONLY level with more than 1 step. L09 has mechanical `refine` + 3 independent `exact` steps. This world does not teach proof construction.

---

## 7. Learner simulation

### 7a. Attentive novice

**First stuck point**: Nowhere. The world is too easy to get stuck on. Every level can be solved by reading the introduction and copying the lemma name into `rw` or `exact`. The novice finishes the world without learning how to combine cardinality lemmas.

**Most likely wrong move**: Typing `rw [Finset.card_insert_of_notMem]` without the hypothesis argument in L03. The hint catches this ("What lemma takes a non-membership proof...?").

**Hint rescue**: Hints work but are unnecessary. The introduction text already gives the lemma name and signature. The hint hidden layer gives the exact code. There is nothing left for the learner to figure out.

**Lesson legibility**: The *stated* lesson of each level is legible (one cardinality lemma per level). The *actual* lesson ("apply one lemma") is the same for every level, so nothing differentiates the learning experience.

**Overall novice experience**: The novice leaves this world knowing the *names* of cardinality lemmas but not how to *use* them in multi-step reasoning. They have never peeled apart a literal finset. They have never combined inclusion-exclusion with a cardinality computation.

### 7b. Experienced Lean user

**Avoidable friction**: None. The world is frictionless because every proof is one step.

**Alias gaps**: None detected.

**Inventory clutter**: Reasonable. 6 new theorems across 8 non-boss levels is appropriate.

**Forced verbosity**: The experienced user will be annoyed that every level is `exact Finset.<lemma> <args>`. There is nothing to engage with. `simp` would close most levels if it weren't disabled (and currently it ISN'T disabled, so the experienced user can literally `simp` through the world).

**Overall experienced user experience**: Boring. The experienced user will `simp`/`norm_num` through every level in under 2 minutes without engaging with any content. Even with `simp` disabled, each level is a single `exact` that any experienced user can produce from the introduction text.

---

## 8. Boss integrity (L09)

### Boss diagnosis: GAUNTLET (Failure taxonomy #8b)

The boss is three independent conjuncts. Each conjunct is a single-lemma application. The proof is:
```
refine <...>
exact Finset.card_range 10
exact Finset.card_union_add_card_inter _ _
exact Finset.card_filter_le _ _
```

There is NO interaction between the parts. There is NO novel integration demand. The learner replays L05, L07, and L08 in sequence. The boss is longer but not harder to *plan* than any individual level.

**Seeded subskills**: Each lemma was introduced in its own level. Technically seeded, but at zero distance (each part IS the earlier level repeated verbatim).

**Closure quality**: POOR. The boss does not test whether the learner can combine lemmas. The most interesting cardinality skill -- chaining `card_insert_of_notMem` to compute the cardinality of a literal finset -- is not tested.

**Integration quality**: ABSENT. The three parts are independent. No part requires output from another part. No part requires combining two or more lemmas.

**Surprise burden**: None. Each part is identical to its origin level.

**Can the learner explain why the proof works?** "I applied the lemma that matches each goal." This is retrieval, not understanding.

### Recommended boss redesign

Replace the boss with a problem that requires genuine integration. Example:

"Given `s = {1, 2, 3}` and `t = {3, 4, 5}`, prove that `(s cup t).card = 5`."

This requires:
1. Using inclusion-exclusion to relate `(s cup t).card` to `s.card`, `t.card`, and `(s cap t).card`.
2. Computing `s.card = 3` and `t.card = 3` (via `card_insert_of_notMem` chaining or `card_range`-adjacent reasoning).
3. Computing `(s cap t).card = 1` (requiring knowledge of what the intersection is).
4. Arithmetic: `3 + 3 - 1 = 5` (or the additive equivalent: solve `5 + 1 = 3 + 3`).

This is a genuine multi-step integration problem that uses inclusion-exclusion, cardinality computation, and arithmetic together.

---

## 9. Course-role sanity

**Intended role**: Lecture world on cardinality.

**Actual role**: Lemma catalog. Each level introduces one lemma via a single application. The world does not teach cardinality *reasoning*; it teaches cardinality *vocabulary*.

A lecture world should build fluency through worked examples, supported practice, and integration. This world has only first-contact introductions. There is no practice, no retrieval, and the boss is a gauntlet.

**Miscast?**: Partially. The world fulfills the "introduce cardinality lemmas" role of its plan, but fails the "lecture" role because a lecture world should build toward independent problem-solving. The plan says the boss should require "Integration of M9, M10, T4" -- the current boss does not integrate anything.

---

## 10. Technical risks

| Risk | Severity | Notes |
|------|----------|-------|
| `simp` not disabled | P0 | Closes 7/9 levels. Add `simp` to `DisabledTactic` on all levels. |
| `norm_num` not disabled | P1 | Closes 6/9 levels. Add `norm_num` to `DisabledTactic` on all levels. |
| Boss is gauntlet (no integration) | P1 | Redesign to require multi-step reasoning. |
| No multi-step proof in any level | P1 | At least one level (ideally 2-3) should require chaining lemmas. |
| Build warnings about TacticDoc | P3 | Info-level, not blocking. The upstream TacticDoc entries cover these. |

---

## 11. Ranked patch list

### P0 (blocking -- must fix before re-audit)

1. **Add `simp` to `DisabledTactic` on ALL levels (L01-L09).** The standard disabled set is `trivial decide native_decide simp aesop simp_all`. Currently missing `simp`. Verified that bare `simp` closes L01, L02, L03 (with `[h]`), L04 (with `[h]`), L05, L06, L07.

2. **Add `norm_num` to `DisabledTactic` on L01, L02, L05, L06, L07, L09.** Verified that `norm_num` closes these levels. On L03, L04 (abstract statements), `norm_num` fails, so it's less critical there but can be added for consistency.

### P1 (high -- fix before shipping)

3. **Add at least one multi-step cardinality computation level.** Example: prove `({1, 2, 3} : Finset Nat).card = 3` by chaining `card_insert_of_notMem` and `card_singleton`. Place between L04 and L05. This exercises the "peel off inserts" pattern that L03 describes but never demonstrates.

4. **Add a disjoint-union cardinality level.** Prove `Disjoint s t -> (s cup t).card = s.card + t.card` using `Finset.card_union_of_disjoint`. Place before the inclusion-exclusion level. This gives the learner the simple case before the general identity.

5. **Redesign the boss to require genuine integration.** Replace the three-conjunct gauntlet with a problem that combines inclusion-exclusion with cardinality computation. Example: "Prove `({1,2,3} cup {3,4,5}).card = 5`" which requires applying inclusion-exclusion, computing individual cardinalities, and doing arithmetic.

6. **Add a concrete inclusion-exclusion computation level after L07.** The learner should compute `({1,2,3} cup {2,3,4}).card` as a specific number, forcing them to combine `card_union_add_card_inter` with cardinality computations.

### P2 (medium -- improve when fixing P1s)

7. **Add a level where the learner produces a non-membership proof.** In L03, `h : a not in s` is given. In practice, the learner must derive non-membership. Add a concrete variant: given `s = {1, 2}`, prove `3 not in s` and then conclude `(insert 3 s).card = s.card + 1`.

8. **`rfl` closes L01 and L05 (definitional).** Cannot disable `rfl`. Accept as known limitation. The `simp` and `norm_num` fixes address the more egregious exploits.

### P3 (low -- nice to have)

9. **Add `card_pos` connection in L01 or L02 conclusion.** Mention that `Finset.card_pos` connects cardinality to nonemptiness. Seeds W12 vocabulary at zero cost.

10. **Add foreshadowing of `card_image_of_injective` in L09 conclusion.** Connects cardinality to the image operation from W8.

11. **Strengthen W10 foreshadowing in L09.** Connect `card_empty`, `card_singleton`, `card_insert_of_notMem` to the base case and inductive step of `Finset.induction_on`.

---

## 12. What to playtest again after patching

1. **All levels (L01-L09)**: Verify `simp` and `norm_num` are now blocked.
2. **New multi-step levels**: Verify they cannot be closed by a single tactic.
3. **Redesigned boss**: Verify it requires genuine integration (multiple lemmas, not just `refine + exact`).
4. **Disjoint-union level**: Verify the statement requires the `Disjoint` hypothesis and is not closable by automation.
5. **New concrete computation levels**: Verify `omega` does not close arithmetic subgoals prematurely. If `omega` can close `1 + 1 + 1 = 3` after rewriting, that may be acceptable (arithmetic is not the lesson), but verify it does not bypass the cardinality rewriting steps entirely.
