# W13 FinsetSum -- Playtest Audit Round 2

**Auditor**: lean4game-playtest-auditor
**World**: W13 FinsetSum (9 levels, L01-L09)
**Round**: R2 (follow-up to R1 which found P1: `norm_num` one-shots L07)
**Date**: 2025-03-15

## R1 Fix Verification

**R1 finding**: `norm_num` one-shots L07 (the concrete computation level). Fix: add `norm_num` to L07's DisabledTactic.

**Verification**: `norm_num` is present in L07's DisabledTactic line:
```
DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
```

**Status**: APPLIED -- but introduces a **P1 regression** (see item 1 below).

---

## 1. Technical Sanity

### Build
Build passes. 8258 jobs, no errors. Informational warnings about missing tactic documentation (using existing docstrings) and dependency warnings (`Finset.disjoint_left`, `Nat`, `Disjoint` not introduced by a prerequisite world).

### DisabledTactic coverage
All 9 levels have `DisabledTactic trivial decide native_decide simp aesop simp_all`. L07 additionally disables `norm_num`. This is consistent across the world.

### Inventory
- 5 `NewTheorem` declarations: `sum_singleton` (L01), `sum_empty` (L02), `sum_cons` (L04), `sum_insert` (L05), `sum_union` (L08)
- All 5 have `TheoremDoc` entries
- No `NewTactic` or `NewDefinition` declarations in this world
- No missing docs for new items

### Dependency warnings (non-blocking)
Build warns that `Finset.disjoint_left`, `Nat`, and `Disjoint` are required by FinsetSum but not introduced by any predecessor world. These are pre-existing dependency graph issues, not new to this world.

---

## 1b. Statement Exploitability

### `rfl` closes 6 of 9 levels (P2 -- known systemic)

Tested every level against `rfl`:

| Level | `rfl` closes? | Notes |
|-------|--------------|-------|
| L01   | YES          | `∑ x ∈ {2}, x = 2` is definitional |
| L02   | YES          | `∑ x ∈ ∅, x^2 = 0` is definitional |
| L03   | YES          | `∑ x ∈ {a}, f x = f a` is definitional (!) |
| L04   | No           | Abstract over `s`, not definitional |
| L05   | No           | Abstract over `s`, not definitional |
| L06   | No           | Commutativity not definitional |
| L07   | YES          | `∑ x ∈ {1,2,3}, x^2 = 14` reduces definitionally |
| L08   | YES          | Both sides reduce to the same concrete value |
| L09   | YES          | Concrete finset, concrete function, definitional |

`rfl` cannot be disabled. This matches the known systemic P2 from MEMORY.md ("Cannot disable `rfl`. Accept as P2."). The learner must already know to try `rfl` on concrete Finset goals, which is non-obvious. **P2 -- accept.**

### `norm_num` closes 5 of 9 levels (P2)

`norm_num` (available since W2 L05) closes L01, L02, L03, L08, and L09. It is NOT disabled on those levels. However:

- L01, L02, L03: These are introductory/practice levels. A learner who uses `norm_num` here misses learning the API lemma, but the lesson is reinforced in later levels (L04, L05 are abstract and immune).
- L08: First-contact for `sum_union`. Using `norm_num` bypasses the lesson entirely.
- L09: Boss. Using `norm_num` bypasses the entire integration exercise.

However, disabling `norm_num` on L08 and L09 would break the **intended proof**, which uses `norm_num [Finset.disjoint_left]` to establish disjointness. The intended proof relies on `norm_num` for subgoals.

**Assessment**: `norm_num` one-shotting concrete Finset.sum goals requires knowing that `norm_num` has Finset.sum extensions -- not obvious to a novice. An experienced user who tries it bypasses the lesson but would already know the API. Since disabling `norm_num` on L08/L09 would break their intended proofs (disjointness needs it), and `rfl` already closes these goals anyway, adding `norm_num` to DisabledTactic here gains nothing. **P2 -- accept for L01, L02, L03, L08, L09.**

---

## 1b-critical. L07 Regression: `norm_num` disabled but hints require it (P1)

The R1 fix added `norm_num` to L07's DisabledTactic. But L07's **intended proof and hints** require `norm_num` in three places:

1. **Line 44 hint**: "Try `have h1 : (1 : Nat) ∉ ... := by norm_num`"
2. **Lines 50-52 hint**: "Use `have h2 : (2 : Nat) ∉ ... := by norm_num`"
3. **Lines 57-58 hint**: "Close with `norm_num`" / "Use `norm_num`"

With `norm_num` disabled, the player cannot follow any of these hints. The membership proofs (`1 ∉ {2, 3}`, `2 ∉ {3}`) require either `norm_num`, `simp`, or `decide` -- all of which are disabled. The manual alternative requires `rw [Finset.mem_insert]` + `push_neg` + `Finset.mem_singleton` + `omega`, which is extremely verbose and completely off-topic for this level.

The final arithmetic (`1^2 + (2^2 + 3^2) = 14`) can be closed by `omega`, but the hints say `norm_num`.

Meanwhile, `rfl` still closes the entire goal in one shot (since Finset.sum over concrete finsets is definitional). So the level IS completable -- but only via the `rfl` exploit, not via the intended pedagogical path.

**This is a P1 regression**: the R1 fix blocks the one-shot exploit (good) but also blocks the intended proof (bad). The hints are misleading -- they tell the player to use a disabled tactic.

**Fix options**:
1. **Remove `norm_num` from L07's DisabledTactic and accept the `norm_num` one-shot as P2** (since `rfl` already one-shots it anyway, blocking `norm_num` gains nothing).
2. **Keep `norm_num` disabled but rewrite the hints** to guide the player through the membership proofs manually (using `intro h` + `rw [Finset.mem_insert] at h` + ...), and change the final arithmetic hint to say `omega`. This is pedagogically worse -- the level becomes about membership reasoning rather than sum decomposition.
3. **Keep `norm_num` disabled and provide membership as hypotheses** in the Statement (i.e., add `(h1 : (1 : Nat) ∉ ({2,3} : Finset Nat)) (h2 : (2 : Nat) ∉ ({3} : Finset Nat))` as parameters). The learner focuses purely on the decomposition pattern. Final arithmetic step uses `omega`.

**Recommendation**: Option 1. Since `rfl` already closes L07 and cannot be disabled, adding `norm_num` to DisabledTactic provides zero additional protection against one-shotting. The R1 fix is strictly harmful. Remove `norm_num` from L07's DisabledTactic.

---

## 1c. Interactive Proof Quality

All levels have single-step tactic proofs or short sequences of `have` + `rw` + `exact`. No elaborate one-liners. No opaque goal states. Hints fire at appropriate points.

**L07**: Multi-step proof (5+ steps) is well-hinted with step-by-step guidance. Each `rw` produces a visible change in the goal. Good interactive quality.

**L09 boss**: Multi-step proof (6+ steps). Hints guide each step. Each `rw` or `exact` produces clear goal-state change. Good.

No issues found.

---

## 2. Coverage Sanity

### Core items coverage

| Item | Axis | Intro | Practice | Retrieval | Integration | Transfer |
|------|------|-------|----------|-----------|-------------|----------|
| `sum_singleton` | MATH+LEAN | L01 | L03, L07 | L09 | L09 | -- |
| `sum_empty` | MATH+LEAN | L02 | -- | -- | -- | -- |
| `sum_cons` | MATH+LEAN | L04 | -- | -- | -- | -- |
| `sum_insert` | MATH+LEAN | L05 | L07 | L09 | L09 | -- |
| `sum_union` | MATH+LEAN | L08 | -- | L09 | L09 | -- |
| AddCommMonoid reason | MATH | L06 | -- | -- | -- | L06 conclusion |
| Sum decomposition pattern | MOVE | L07 | -- | L09 | L09 | L09 conclusion |

### Coverage gaps (minor)
- `sum_empty` and `sum_cons` have no retrieval or integration after introduction. They appear once and are never used again. The enrichment reviewer (R1, R2) noted this; the plan assigns retrieval to W14 (induction base case for `sum_empty`) and later worlds. **P3 -- acceptable for this world in isolation.**
- No example on non-Nat types (Int, Rat). Mentioned in prose but never exercised. Plan assigns to later worlds. **P3.**

### Transfer
L06 conclusion and L09 conclusion both provide plain-language transfer moments. L09's conclusion connects the Lean decomposition pattern to hand-computation. Adequate.

---

## 3. Granularity Sanity

### Level-by-level assessment

| Level | Role | Dominant Lesson | Scope |
|-------|------|----------------|-------|
| L01 | Introduction | Big-sum notation + `sum_singleton` | Appropriate |
| L02 | Introduction | `sum_empty` | Appropriate |
| L03 | Practice | `sum_singleton` with explicit function | Appropriate |
| L04 | Introduction | `sum_cons` | Appropriate |
| L05 | Introduction | `sum_insert` | Appropriate |
| L06 | Conceptual | Why AddCommMonoid is needed | Appropriate |
| L07 | Practice | Step-by-step concrete computation | Appropriate |
| L08 | Introduction | `sum_union` for disjoint sets | Appropriate |
| L09 | Boss | Integration of all decomposition tools | Appropriate |

### World center of gravity
Stable: "decomposition lemmas for Finset.sum." Every level contributes to this theme.

### Boss seeding
L09 requires: `sum_union` (L08), `sum_insert` (L05), `sum_singleton` (L01, L03), and arithmetic. All subskills are introduced and practiced before the boss. No untaught microskills in the boss. However, the boss does NOT require `sum_empty` or `sum_cons` -- these are taught but never integrated. This was flagged in R1 enrichment as a "yes" item. The enrichment R2 downgraded it to "consider."

### Boss quality
The boss is a **gauntlet** rather than a true integration challenge: it concatenates `sum_union` + `sum_insert` + `sum_singleton` sequentially. Each step is independent -- the learner replays individual levels in sequence without needing to see the whole structure. However, the combination of `sum_union` (which requires establishing disjointness) with `sum_insert` (which requires establishing non-membership) does create some planning challenge. **Borderline P3** -- the boss is adequate but not rich.

---

## 4. Learner Simulation

### Attentive novice

**First likely stuck point**: L07. The multi-step proof with `have` + `rw` sequences is the most complex in the world. The novice may not know how to state the `have` with the right type annotation.

**Most likely wrong move on L07**: Trying `rw [Finset.sum_insert]` without first establishing the membership proof. Lean will ask for the membership proof as a goal, which may confuse the novice.

**Hint rescue**: Good. L07 hints explicitly tell the learner to establish membership first, then rewrite. The step-by-step guidance is thorough.

**Legibility**: High for L01-L06, L08. L07 and L09 require more sophistication (multi-step proofs with intermediate `have` statements) but hints compensate.

**L07 with `norm_num` disabled**: If the novice follows the hints (which say "use `norm_num`"), they will be stuck because `norm_num` is disabled. This is the P1 regression. Without the regression, the novice path through L07 is well-guided.

### Experienced Lean user

**Avoidable friction**: None significant. The levels are clean and direct.

**`rfl` shortcut**: An experienced user will notice that all concrete-finset levels can be closed by `rfl`. This is a known P2 systemic issue.

**`norm_num` shortcut**: An experienced user who knows `norm_num` handles Finset.sum may try it on L01, L02, L03, L08, L09 and succeed. P2.

**Inventory clutter**: Low. Only 5 new theorems, all well-documented.

**Forced verbosity**: L07 is the most verbose level (5+ steps) but this is intentional -- the point is to show the decomposition mechanics.

---

## 5. Course-role Sanity

| Level | Intended Role | Actual Role | Match? |
|-------|--------------|-------------|--------|
| L01 | Introduction | Introduction | YES |
| L02 | Introduction | Introduction | YES |
| L03 | Practice | Practice | YES |
| L04 | Introduction | Introduction | YES |
| L05 | Introduction | Introduction | YES |
| L06 | Conceptual/Transfer | Conceptual/Transfer | YES |
| L07 | Practice (concrete) | Practice (concrete) | YES |
| L08 | Introduction | Introduction | YES |
| L09 | Boss | Boss (borderline gauntlet) | YES (marginal) |

No miscast levels.

---

## Overall Verdict

**CONDITIONAL PASS** -- one P1 defect (regression from R1 fix).

## Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | `sum_empty` and `sum_cons` lack same-world retrieval (deferred to W14) |
| 2. Granularity fit | 3 | Clean level ladder, each level has one dominant lesson |
| 3. Proof-move teaching | 3 | Decomposition pattern well-taught; `have` for intermediate proofs practiced |
| 4. Inventory design | 4 | 5 theorems, all documented, clean progression |
| 5. Hint design | 2 | L07 hints reference disabled tactic (P1 regression) |
| 6. Progression | 3 | Good ladder; boss is adequate but not rich |
| 7. Mathematical authenticity | 3 | Good explanations; all examples use Nat only |
| 8. Paper-proof transfer | 3 | L06 and L09 conclusions provide transfer moments |
| 9. Technical fit | 3 | Build clean; L07 regression is the main issue |
| **Average** | **3.0** | |

## Coverage Gaps

1. `sum_empty` never retrieved after introduction (L02). Retrieval deferred to W14. P3.
2. `sum_cons` never retrieved after introduction (L04). Retrieval deferred to later worlds. P3.
3. No non-Nat examples of Finset.sum. Deferred to later worlds. P3.

## Granularity Defects

None significant.

## Learner Simulation Notes

- L07 is the critical path. With the `norm_num` regression fixed, the novice experience is clean.
- Experienced users can `rfl` everything concrete. Known P2.
- No new exploitation paths beyond those documented above.

## Boss Integrity Notes

- Boss integrates `sum_union` + `sum_insert` + `sum_singleton` + disjointness + arithmetic.
- Boss does NOT require `sum_empty` or `sum_cons`. This was flagged in enrichment R1 and downgraded in R2.
- Boss is borderline gauntlet: steps are largely independent. Some planning challenge from disjointness establishment.
- No untaught microskills in the boss. All subskills introduced and practiced.

## Technical Risks

1. **P1**: L07 hints tell player to use `norm_num` but `norm_num` is disabled. Intended proof path is broken.
2. **P2**: `rfl` closes L01, L02, L03, L07, L08, L09 (systemic, known, cannot fix).
3. **P2**: `norm_num` closes L01, L02, L03, L08, L09 (not disabled on those levels; disabling would break intended proofs on L08/L09).

## Ranked Patch List

### 1. [P1] Remove `norm_num` from L07's DisabledTactic (regression fix)

**File**: `Game/Levels/FinsetSum/L07_ConcreteSum.lean` line 82
**Change**: Remove `norm_num` from `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num`
**Rationale**: The R1 fix blocked the one-shot but also blocked the intended proof. Since `rfl` already one-shots L07 (and cannot be disabled), blocking `norm_num` provides zero additional protection. Remove it to restore the intended pedagogical path where the learner uses `norm_num` only for membership subgoals and final arithmetic, while the decomposition steps (`sum_insert`, `sum_singleton`) teach the lesson.

---

## What to Playtest Again After Patching

After removing `norm_num` from L07's DisabledTactic:
- Verify L07's full intended proof path works with hints
- Confirm no new P0/P1 issues
- If clean, the world passes (P2 issues are systemic and accepted)
