# W2 FinCompute -- Playtest Audit (Round 2)

**World**: W2 FinCompute (11 levels, re-authored)
**Role**: Lecture world -- introduces `fin_cases`, `decide`, `norm_num`, modular arithmetic, exhaustive verification, function computation on `Fin`
**Prerequisite**: W1 FinIntro (13 levels)
**Auditor posture**: Adversarial. This is the second audit; all P0 and P1 issues from the first audit must be verified as genuinely fixed.

---

## 0. Prior-Audit Regression Check

The first audit identified 2 P0, 4 P1, 6 P2, and 2 P3 defects. Below is the status of every one.

### P0 issues (blocking)

| ID | First-audit defect | Status | Evidence |
|----|-------------------|--------|----------|
| P0-1 | **Statement exploitability**: Every level after L03 solvable by `decide` | **FIXED (partial)** | `decide` is now disabled via `DisabledTactic decide` on L01, L02, L04, L05, L06, L08, L10. Levels L07 and L09 intentionally use `decide` as the intended tactic (modular arithmetic). L03 intentionally teaches `decide`. **However**, see new P0-1 below: `native_decide` is never disabled and closes every single level. |
| P0-2 | **Missing TacticDoc**: `fin_cases`, `decide`, `norm_num` had no documentation | **FIXED** | `TacticDoc fin_cases` in L01 (lines 52-62), `TacticDoc decide` in L03 (lines 46-62), `TacticDoc norm_num` in L05 (lines 44-57). All include purpose, syntax, examples, and when-to-use guidance. |

### P1 issues (high)

| ID | First-audit defect | Status | Evidence |
|----|-------------------|--------|----------|
| P1-1 | **Gauntlet boss**: L08 used same `fin_cases <;> closer` pattern with no novel integration | **FIXED** | The new boss (L11) requires `constructor` to split a conjunction, then `decide` for a modular arithmetic equality, then `intro i; fin_cases i <;> norm_num` for a universal property. The two parts demand different proof strategies. This is genuine integration, not a gauntlet. |
| P1-2 | **L07 plan mismatch**: Plan said "build a function" but implementation just proved a universal property | **PARTIALLY ADDRESSED** | New L08 (FunctionOnFin) involves computing a sum of function outputs, which is a different proof shape from L01-L06. However, the learner does not *define* a function by cases (V19) -- the statement is still a concrete numeric computation closed by `norm_num`. The plan's V19 ("define a function `Fin 3 -> Nat` by cases") is not genuinely taught. See P2-1. |
| P1-3 | **`norm_num` has no supported practice**: Went from introduction to boss directly | **FIXED** | New L06 (NormNumPractice) provides supported practice combining `fin_cases` and `norm_num`. L08 (FunctionOnFin) provides a second practice opportunity. L10 (MixedTactics) provides a third. The path from introduction (L05) through practice (L06, L08, L10) to boss (L11) is now well-paved. |
| P1-4 | **No Branch alternatives**: L04 told learners to "try both approaches" but had no Branch | **NOT FIXED** | No `Branch` declarations exist anywhere in the world. However, this is now a lower-severity issue than before: L04 no longer tells learners to "try both approaches" (the introduction says "decide is disabled"). The misleading text is gone. But L07 and L09 (where `decide` is the intended tactic) could benefit from `Branch` for `norm_num`, and the boss could benefit from `Branch` for the second conjunct. Downgraded to P2. |

### P2 issues (medium)

| ID | First-audit defect | Status | Evidence |
|----|-------------------|--------|----------|
| P2-1 | **L01/L02 near-clones** | **FIXED** | L01 introduces `fin_cases` with separate `omega` closings per case. L02 introduces the `<;>` combinator as a distinct new lesson. These are now genuinely different levels with different dominant lessons. |
| P2-2 | **L04 does not teach tactic selection**: `decide` and `fin_cases` interchangeable | **FIXED** | L04 explicitly disables `decide` and frames the lesson as "when you need per-case control that `decide` cannot give." The conclusion provides a clear three-strategy comparison table. The learner is forced to use `fin_cases` and see why it is needed. |
| P2-3 | **Modular arithmetic (M4) has only one level** | **FIXED** | Now has two dedicated levels: L07 (subtraction wrapping) and L09 (multiplication wrapping). Both cover distinct "surprise" aspects of modular arithmetic. |
| P2-4 | **Hint design is thin**: All hints gave answers immediately | **PARTIALLY FIXED** | Most levels now have a visible strategy hint followed by a hidden code hint. For example, L01 has "Start with `intro i`" (visible), then "After `fin_cases i`, you will have three separate goals. Close each one with `omega`" (hidden). However, some levels still have thin hint design -- see P2-3 below. |
| P2-5 | **Conjunction (`and`) in boss is untaught micro-burden** | **FIXED** | L04 now introduces conjunction (`∧`) in a `fin_cases` context. The boss uses `constructor` which was taught in W1. The path is: `constructor` from W1 -> conjunction in L04 -> boss conjunction in L11. |
| P2-6 | **`omega` can close L05** | **FIXED** | L05 now disables both `decide` AND `omega` (`DisabledTactic decide omega`), forcing the learner to use `norm_num`. The statement involves `^` which `omega` cannot handle anyway, but the explicit disable is a belt-and-suspenders fix. |

### P3 issues (low)

| ID | First-audit defect | Status | Evidence |
|----|-------------------|--------|----------|
| P3-1 | **No transfer level** | **NOT FIXED** | There is still no explicit transfer level. Transfer text appears in conclusions (L01, L07, L08, L11), which is good, but no level asks the learner to demonstrate understanding in a different form. However, this is appropriate for a lecture world -- the transfer is deferred to W3_ex (Example world) per the plan. Not a defect. |
| P3-2 | **Boss conclusion too brief** | **FIXED** | L11's conclusion now includes a detailed tactic summary table, a pattern summary, and a paper-proof transfer paragraph. |

### Regression summary

- **P0**: 1 of 2 genuinely fixed (P0-2). P0-1 is fixed for `decide` but a new variant (P0-1b: `native_decide`) replaces it.
- **P1**: 3 of 4 fixed (P1-1, P1-3, P1-4 downgraded). P1-2 is partially addressed but V19 is still not taught.
- **P2**: 5 of 6 fixed. P2-4 partially fixed.
- **P3**: Both addressed (one fixed, one correctly deferred).

---

## 1. Technical Sanity

### 1a. Build/import issues

None. The project builds successfully (8117 jobs, no errors). All 11 level files are correctly imported in `FinCompute.lean`. Level numbering is consecutive (1-11).

### 1b. Statement Exploitability

#### `native_decide` bypass -- **P0 (BLOCKING)**

**Every level in the world is closable by `native_decide`**, which is never disabled.

Verified by testing each statement:

| Level | Intended tactic | `native_decide` works? |
|-------|----------------|----------------------|
| L01 | `fin_cases i <;> omega` | Yes |
| L02 | `fin_cases i <;> omega` | Yes |
| L03 | `decide` | Yes (expected) |
| L04 | `fin_cases i <;> omega` | Yes |
| L05 | `norm_num` | Yes |
| L06 | `fin_cases i <;> norm_num` | Yes |
| L07 | `decide` | Yes (expected) |
| L08 | `norm_num` | Yes |
| L09 | `decide` | Yes (expected) |
| L10 | `fin_cases i <;> norm_num` | Yes |
| L11 (Boss) | `constructor; decide; intro i; fin_cases i <;> norm_num` | Yes |

A learner who discovers `native_decide` can complete the entire world without engaging with `fin_cases`, `norm_num`, or any intended proof pattern. `native_decide` is strictly more powerful than `decide` -- it uses native code evaluation, so it is fast even on larger types.

**Fix**: Add `DisabledTactic native_decide` to every level in the world (including L03, L07, L09 where `decide` is intended -- `decide` and `native_decide` are separate tactics).

#### `decide` on the boss (L11) -- **P0 (BLOCKING)**

The boss (L11) does not disable `decide`. The entire statement `((3 : Fin 5) + (4 : Fin 5) = (2 : Fin 5)) ∧ (∀ i : Fin 5, i.val ^ 2 < 20)` is a decidable proposition. Verified: `decide` closes it in one shot.

The boss introduction says "decide is disabled for this goal" for part 2, but the `DisabledTactic decide` line is **absent** from L11. The learner can type `decide` and solve the entire boss without `constructor`, `fin_cases`, or `norm_num`.

This is a P0 defect because it completely undermines the boss's integration purpose.

**Fix**: The boss must decide (pun intended) on one of two approaches:
1. Disable `decide` entirely and require the learner to use `constructor`, then solve part 1 with `norm_num` (which can handle the modular equality) and part 2 with `fin_cases <;> norm_num`. This loses the integration of `decide` as a distinct tool for part 1.
2. (Better) Do not disable `decide`, but redesign the boss so that `decide` cannot close the whole thing. For example, add a component that is not decidable, or that `decide` times out on. Or disable `decide` and add a `Branch` for the first conjunct that accepts `norm_num` (since `norm_num` can evaluate `(3 : Fin 5) + (4 : Fin 5)` to `(2 : Fin 5)`).

The simplest correct fix: add `DisabledTactic decide native_decide` to L11, and change the hint for part 1 from "Use `decide`" to "Use `norm_num`" (which does close it). This forces `constructor; norm_num; intro i; fin_cases i <;> norm_num`.

### 1c. Interactive proof quality

The re-authored world has improved interactive quality. Assessment per level:

| Level | Proof shape | Interactive quality |
|-------|------------|-------------------|
| L01 | `intro i; fin_cases i; omega; omega; omega` | Good. Each step produces visible change. Learner sees goals split. |
| L02 | `intro i; fin_cases i <;> omega` | Good. `<;>` is explicitly taught. |
| L03 | `decide` | Good. One tactic, clear result. |
| L04 | `intro i; fin_cases i <;> omega` | Good. |
| L05 | `norm_num` | Good. One tactic, clear result. |
| L06 | `intro i; fin_cases i <;> norm_num` | Good. |
| L07 | `decide` | Good. One tactic. |
| L08 | `norm_num` | Good. One tactic. |
| L09 | `decide` | Good. One tactic. |
| L10 | `intro i; fin_cases i <;> norm_num` | Good. Intro discusses per-case handling. |
| L11 | `constructor; decide; intro i; fin_cases i <;> norm_num` | Good. Multi-step with visible state changes. |

No elaborate one-liners, no opaque goals. This passes.

### 1d. Missing documentation

All three new tactics (`fin_cases`, `decide`, `norm_num`) have proper `TacticDoc` entries. Each includes:
- What the tactic does
- Example usage
- When to use / when not to use
- Comparison with alternatives

This passes.

### 1e. `simp_all` reference in L10

L10's introduction mentions "the tactic `simp_all` or a combination `<;> first | omega | norm_num`" as alternatives. Neither `simp_all` nor `first` has been introduced. This is not a blocking issue (it's informational text, not a hint), but it could confuse a novice who tries `simp_all` and it works, bypassing the intended proof. Minor risk.

**Recommendation (P3)**: Remove the `simp_all` mention or note that it is an advanced tactic not yet available.

---

## 2. Coverage Sanity

### 2a. Core items coverage

| Item | Plan ID | Coverage state in W2 | Assessment |
|------|---------|---------------------|------------|
| `fin_cases` | L4 | I (L01), S (L02, L04, L06, L10), G (L11) | **Good**. Introduction, four supported practice levels, boss integration. |
| `<;>` combinator | -- | I (L02), S (L04, L06, L10), G (L11) | **Good**. Dedicated introduction level, used throughout. |
| `decide` | L3 | I (L03), S (L07, L09), G (L11) | **Good**. Introduction, two practice levels (modular arithmetic), boss integration. |
| `norm_num` | L6 | I (L05), S (L06, L08, L10), G (L11) | **Good** (was P1-3). Now has three supported practice levels before boss. |
| Modular arithmetic (M4) | M4 | I (L07), S (L09) | **Improved** (was P2-3). Two levels covering subtraction and multiplication wrapping. |
| Conjunction `∧` | -- | I (L04), G (L11) | **Adequate**. Introduced in L04, used in boss. `constructor` from W1. |
| Tactic selection meta-skill | V2 | I (L04), S (L10) | **Improved**. L04 frames the choice, L10 exercises mixed closers. |

### 2b. Coverage gaps

1. **V19 (recursive/inductive construction on Fin) is still not taught.** The plan specifies W2.7 as "Building a function on `Fin n`: Define a function `Fin 3 -> Nat` by cases." L08 (FunctionOnFin) computes a sum of function outputs, which is norm_num practice on a concrete expression -- not function construction. The title says "Defining and Verifying Functions on `Fin n`" but the learner neither defines nor constructs a function; they evaluate a numeric expression. V19 remains unaddressed. This is a plan deviation, not necessarily a world defect -- the question is whether V19 belongs in this world or should be deferred to W3_ex. **Severity: P2** (plan mismatch, but no learner-facing harm).

2. **No level where `decide` fails and `fin_cases` is needed.** L04 teaches the tactic-selection meta-skill by disabling `decide`, but the learner never *experiences* `decide` failing. They are told "decide is disabled" and use `fin_cases`. A stronger lesson would show `decide` genuinely timing out or failing on a larger type (e.g., `Fin 50`), making the need for `fin_cases` visceral. **Severity: P3** (pedagogical nicety, not a gap).

### 2c. Proof-move coverage

The world teaches two proof moves:
1. **Exhaustive case analysis** (`fin_cases` pattern): well-covered across L01, L02, L04, L06, L10.
2. **Computational verification** (`decide`, `norm_num`): well-covered across L03, L05, L07, L08, L09.

The integration of these two patterns (L11 boss) is genuine.

### 2d. Example coverage

The world uses concrete `Fin n` types: `Fin 3` (L01, L08, L10), `Fin 4` (L02, L04, L06, L09), `Fin 5` (L07, L11), `Fin 10` (L05). Good variety. Modular arithmetic is concretized on two specific examples (subtraction wrapping in Fin 5, multiplication wrapping in Fin 4). The zero-divisor concept in L09's conclusion (mentioning `2 * 2 = 0` in `Fin 4`) adds mathematical depth.

### 2e. Transfer coverage

Transfer text appears in:
- L01 conclusion: "In plain language: There are exactly three elements..."
- L07 conclusion: "In plain language: Arithmetic in Z/5Z..."
- L08 conclusion: "Transfer to paper proofs: exactly what a mathematician means..."
- L11 conclusion: "We prove two facts. First, 3 + 4 = 2 (mod 5)..."

No dedicated transfer *level*, but this is appropriate for a lecture world. Transfer levels are deferred to W3_ex per the plan.

---

## 3. Granularity Sanity

### 3a. Level-by-level granularity

| Level | Dominant lesson | Assessment |
|-------|----------------|-----------|
| L01 | Introducing `fin_cases` | **Good**. One new tactic, simple math. |
| L02 | `<;>` combinator | **Good**. Distinct new lesson (syntax combinator). |
| L03 | Introducing `decide` | **Good**. One new tactic, simple statement. |
| L04 | When `decide` doesn't help (forced `fin_cases`) | **Good**. Adds conjunction as mild new burden, but `omega` handles it. |
| L05 | Introducing `norm_num` (powers) | **Good**. One new tactic, clear contrast with `omega`. |
| L06 | `fin_cases` + `norm_num` combination | **Good**. Supported practice for the combination. |
| L07 | Modular subtraction wrapping | **Good**. New math concept, simple tactic (`decide`). |
| L08 | Function output computation | **Adequate**. Title overpromises ("Defining and Verifying"), but the proof experience is valid norm_num practice. |
| L09 | Modular multiplication wrapping | **Good**. Second modular arithmetic example with mathematical insight (zero divisors). |
| L10 | Mixed tactics / per-case handling | **Good**. Teaches the skill of choosing closers per case. |
| L11 | Boss: multi-strategy integration | **Good**. Genuine integration requiring `constructor`, `decide`, `fin_cases`, `norm_num`. |

### 3b. Clone detection

No clone pairs. L01 and L02 are now genuinely different (separate closings vs. `<;>` combinator). L07 and L09 are both modular arithmetic but cover different operations (subtraction vs. multiplication) with different mathematical insights.

### 3c. Center of gravity

The world's center is "computing with `Fin n` using exhaustive case analysis and computational automation." The 11 levels cover:
- Exhaustive verification: L01, L02, L04, L06, L10 (5 levels)
- Computational automation: L03, L05, L07, L08, L09 (5 levels)
- Integration: L11 (1 level)

This is balanced. The center of gravity is stable and coherent.

### 3d. World size

11 levels. This is appropriate for the scope: three new tactics, modular arithmetic, function computation, mixed tactics, and a boss. No level feels redundant; each has a distinct lesson.

---

## 4. Learner Simulation

### 4a. Attentive novice

**First stuck point**: L01. After `intro i`, the novice sees `i.val < 10` with `i : Fin 3`. The introduction explains `fin_cases i`, and the hint says "Use `fin_cases i` to split into cases." The novice has the `TacticDoc` panel available. **Assessment**: The stuck point is well-rescued. The layered hints (visible: "use `fin_cases i`", hidden: "close each one with `omega`") guide without spoiling.

**Most likely wrong move**: After L03, the novice may try `decide` on L04. They will get an error because `decide` is disabled. The introduction explains this: "Notice that `decide` is disabled for this level." **Assessment**: Good handling. The novice learns that `decide` is not always available and must reach for `fin_cases`.

**L05 potential confusion**: The novice may try `omega` (which they know from L01-L02). `omega` is disabled, so they get an error. The introduction explicitly says "omega cannot handle powers" and the hint says "Try `norm_num`." **Assessment**: Good rescue path. The disable-plus-explain pattern is effective.

**L10 potential confusion**: The introduction mentions `simp_all` and `<;> first | omega | norm_num`. A curious novice may try `simp_all`, which is not disabled. If it works, they bypass the lesson. Low severity (the level's lesson is "per-case handling" which the introduction explains regardless).

**L11 (Boss) experience**: The novice sees `P ∧ Q`. The hint says "Use `constructor`." After splitting, they have two goals. The first hint says "Use `decide`." The second says "Use `intro i; fin_cases i <;> norm_num`." **Assessment**: Well-guided. But if `decide` is not disabled (see P0-2), the novice might try `decide` on the whole thing before `constructor` and succeed -- learning nothing.

**Overall novice path**: The novice will have a clean progression through the world IF the P0 exploitability issues are fixed. Without fixes, the novice can `native_decide` everything.

### 4b. Experienced Lean user

**Avoidable friction**: None significant. The proofs are short (1-3 lines). The experienced user will appreciate the `<;>` combinator lesson.

**Exploit awareness**: An experienced user will immediately try `decide` or `native_decide` on every level. They will find that `decide` is properly disabled in most levels, but `native_decide` always works. An experienced user who knows `native_decide` can complete the entire world in under a minute without reading any introduction text.

**Inventory assessment**: Clean. Only three tactics added (`fin_cases`, `decide`, `norm_num`), all well-documented. No clutter.

**Mathematical depth**: L07 and L09's modular arithmetic coverage, including the zero-divisor observation in L09's conclusion, provides genuine mathematical insight that an experienced user would appreciate. The clock-arithmetic analogy in L07 is good.

---

## 5. Boss Integrity Check (L11)

### 5a. Statement

```lean
Statement : ((3 : Fin 5) + (4 : Fin 5) = (2 : Fin 5)) ∧
    (∀ i : Fin 5, i.val ^ 2 < 20) := by
```

### 5b. Seeded subskills

| Subskill | Where seeded | Assessment |
|----------|-------------|------------|
| `constructor` | W1 (baseline) | OK |
| `decide` | L03, L07, L09 | Good (3 prior uses) |
| `fin_cases` | L01, L02, L04, L06, L10 | Good (5 prior uses) |
| `norm_num` | L05, L06, L08, L10 | Good (4 prior uses, was 1 in first audit) |
| Modular arithmetic | L07, L09 | Good (2 prior uses) |
| Conjunction `∧` | L04 | Adequate (1 prior use, but `constructor` is W1 baseline) |
| Powers `^` | L05, L06, L08, L10 | Good (4 prior uses) |

### 5c. Surprise burdens

None. Every component of the boss proof has been practiced in at least one prior level. The conjunction was used in L04. The modular arithmetic was practiced in L07 and L09. The `fin_cases <;> norm_num` pattern was practiced in L06 and L10.

### 5d. Integration quality

**PASS**. This is a genuine integration boss, not a gauntlet:

1. The learner must *plan*: recognize the conjunction structure and use `constructor`.
2. The learner must *select tactics*: `decide` for the concrete equality (part 1), `fin_cases <;> norm_num` for the universal property (part 2).
3. The two parts require *different proof strategies*, so the learner cannot apply a single pattern mechanically.

This addresses the first audit's P1-1 (gauntlet boss) defect. The boss now requires three distinct moves (`constructor`, `decide`, `fin_cases + norm_num`) and the learner must see the proof's structure to know which move goes where.

### 5e. Could the learner explain why the proof works?

Yes: "We prove two things. First, 3 + 4 = 2 in mod 5 arithmetic, which we verify by computation. Second, for every element i in {0,1,2,3,4}, i^2 < 20 -- we check all five cases: 0, 1, 4, 9, 16, all less than 20."

This is a richer explanation than the first-audit boss ("I checked all five cases and norm_num verified each one").

### 5f. Exploitability (CRITICAL)

The boss is completely exploitable by both `decide` and `native_decide`. Neither is disabled. See P0-1 and P0-2 above.

---

## 6. Course-Role Sanity

The world is cast as a **lecture** world. Assessment:

| Criterion | Met? | Notes |
|-----------|------|-------|
| Introduces new material | Yes | Three new tactics, modular arithmetic, function computation |
| Provides supported practice | Yes | Multiple levels per tactic (was a defect, now fixed) |
| Practice is graduated | Yes | Simple -> combined -> mixed -> boss |
| Boss integrates | Yes | Multi-strategy boss (was gauntlet, now fixed) |
| Transfer moments exist | Yes | In conclusions (appropriate for lecture world) |

The world plays its lecture role well. It has moved from "button demo" (first-audit assessment) to "genuine lesson with graduated practice and meaningful integration."

---

## 7. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Core items well-covered through I/S/G. V19 not taught (plan mismatch). |
| 2. Granularity fit | 4 | Each level has a distinct dominant lesson. No clones. World is coherent. |
| 3. Proof-move teaching | 3 | Exhaustive verification and computational automation taught and practiced. Tactic selection meta-skill covered. |
| 4. Inventory design | 3 | Three new tactics, all documented, properly gated. Only defect: `native_decide` not disabled. |
| 5. Hint design & recoverability | 3 | Layered hints (visible + hidden) in most levels. Common wrong moves rescued (try omega, it fails, use norm_num). |
| 6. Worked example -> practice -> transfer -> boss | 3 | Clear progression I -> S -> G for each tactic. Transfer in conclusions. Boss integrates. |
| 7. Mathematical authenticity | 4 | Modular arithmetic well-motivated. Zero divisor insight. Clock analogy. Mathematical stakes clear. |
| 8. Paper-proof transfer | 3 | Consistent transfer language in conclusions. Boss conclusion translates proof to English. |
| 9. Technical fit & maintainability | 2 | `native_decide` exploit is a blocking technical defect. Otherwise clean. |

**Average: 3.1** -- above the 3.0 threshold, but the exploitability defect in category 9 is a red flag that blocks the "good" verdict.

---

## 8. Overall Verdict

**CONDITIONAL PASS** -- the world is pedagogically sound and addresses all first-audit P0 and P1 issues in substance, with one critical exception: `native_decide` is never disabled and closes every level. The boss also fails to disable `decide`. These exploitability defects are the only blocking issues. Once fixed, the world is shippable.

The re-authoring improved the world significantly:
- From 8 to 11 levels, with no padding -- each new level fills a genuine gap.
- The gauntlet boss is replaced by a genuine integration boss.
- `norm_num` coverage closure is now solid (4 practice opportunities before boss).
- Modular arithmetic coverage expanded from 1 to 2 levels.
- All three tactics have proper documentation.
- Level clones eliminated.
- Hint design improved throughout.

**What remains**: Fix the two exploitability defects (P0-1, P0-2 below), add a few `Branch` alternatives, and correct L08's title/framing.

---

## 9. Ranked Patch List

### P0 -- Blocking

| # | Defect | Fix |
|---|--------|-----|
| P0-1 | **`native_decide` bypass**: `native_decide` is never disabled and closes every level in the world. A learner who discovers it can bypass all intended proof patterns. | Add `DisabledTactic native_decide` to **every** level file (L01-L11). In levels where `decide` is also disabled (L01, L02, L04, L05, L06, L08, L10), update to `DisabledTactic decide native_decide`. In levels where `decide` is intended (L03, L07, L09), add a separate line `DisabledTactic native_decide`. |
| P0-2 | **Boss (`L11`) missing `DisabledTactic decide`**: The boss introduction says "decide is disabled for this goal" (for part 2), but `decide` is not actually disabled. `decide` closes the entire boss in one shot, bypassing `constructor`, `fin_cases`, and `norm_num`. | **Option A** (simplest): Add `DisabledTactic decide native_decide` to L11 and change the part-1 hint from "Use `decide`" to "Use `norm_num`" (which can evaluate the modular equality). Update the introduction and conclusion to match. **Option B** (preserves decide integration): Keep `decide` enabled but redesign the boss so that `decide` cannot close the whole thing -- e.g., include a universal quantifier over `Fin 50` where `decide` times out. Option A is recommended for simplicity. |

### P2 -- Medium

| # | Defect | Fix |
|---|--------|-----|
| P2-1 | **V19 (function construction) not taught**: L08 title says "Defining and Verifying Functions on Fin" but the learner does not define a function by cases. They evaluate a concrete numeric expression. | Either (a) rename L08 to "Computing function values" and remove the "Defining" framing, accepting that V19 is deferred to W3_ex; or (b) redesign L08 to have the learner actually construct a function using `fun i => Fin.cases ... ... i` or a `match` expression. Option (a) is simpler and honest. |
| P2-2 | **No `Branch` alternatives anywhere**: The world has no `Branch` declarations, so alternative correct approaches are not validated. | Add `Branch` for: (a) L07: `norm_num` as alternative to `decide`; (b) L09: `norm_num` as alternative to `decide`; (c) L11 part 2: individual case handling as alternative to `<;> norm_num`. Low urgency -- the current intended proofs work and hints point to them. |
| P2-3 | **L07 and L09 hints are minimal**: Both have only "Try `decide`" as visible hint. No layered hint explaining why `decide` works here. | Add a strategy hint to L07 and L09 explaining the reasoning: "This is a concrete equality in `Fin n`. Both sides are specific values, so Lean can evaluate them. What tactic evaluates decidable propositions?" |

### P3 -- Low

| # | Defect | Fix |
|---|--------|-----|
| P3-1 | **L10 mentions `simp_all`**: The introduction references `simp_all` which is untaught and could bypass the intended proof. | Remove the `simp_all` mention or replace with "a combination like `<;> first | omega | norm_num`" only (without naming `simp_all`). Or add `DisabledTactic simp_all` to L10. |
| P3-2 | **L08 conclusion says "In later worlds, you will learn `Finset.sum`"**: This forward reference is helpful but slightly misleading since L08's statement is not actually a `Finset.sum` -- it is a manual sum of three terms. | Rephrase to: "In later worlds, you will learn `Finset.sum`, which expresses this kind of sum over all elements of a finite type directly in Lean notation." (Minor wording change for accuracy.) |

---

## 10. What to Playtest Again After Patching

After implementing the P0 fixes:

1. **`native_decide` and `decide` blocking**: Verify that `native_decide` is disabled in all 11 levels and `decide` is disabled in all levels except L03, L07, L09. Test each level to confirm neither bypass tactic works where disabled.

2. **Boss (L11) under Option A**: If `decide` is disabled in the boss, verify that `norm_num` closes the first conjunct (modular equality). Walk the full boss proof: `constructor; norm_num; intro i; fin_cases i <;> norm_num`. Verify hints and introduction text match the new intended proof.

3. **No other one-shot bypasses**: After fixing `native_decide`, re-check whether `simp`, `aesop`, `tauto`, or any other automation tactic can close levels where it shouldn't. (Based on testing, `simp` does not close these goals, but this should be re-verified after the fix.)

4. **Boss integration quality**: After fixing exploitability, simulate the boss as a novice using only taught tactics. Verify the proof requires genuine planning (which tactic for which subgoal) and cannot be solved by a single repeated pattern.

---

## Summary

The re-authored world is substantially improved. The first audit's systemic problems (clone levels, gauntlet boss, missing documentation, no `norm_num` practice, thin modular arithmetic coverage) are all genuinely fixed. The world now has a coherent progression, distinct levels, a real integration boss, and proper documentation.

The single critical remaining issue is exploitability via `native_decide` (and `decide` on the boss). This is a mechanical fix -- add `DisabledTactic native_decide` everywhere, and handle `decide` on the boss. Once these are applied and verified, the world passes.
