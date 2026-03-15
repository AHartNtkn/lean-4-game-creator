# W8_ex FinsetExploration -- Playtest Audit R2

**World**: FinsetExploration (W8_ex)
**Role**: Example (7 levels)
**Topic**: Concrete exploration of finset operations on {1, 2, 3, 4, 5}: construction, membership, filter, image, powerset preview, product preview, boss integration
**Predecessor**: W8 FinsetTransformations (Lecture)
**Changes since R1**: Added `NewTactic rintro ring` and `TacticDoc rintro`, `TacticDoc ring` to L04.

---

## 1. Overall Verdict

**NEEDS REVISION.** The R1 fix (adding `NewTactic rintro ring` + TacticDoc entries in L04) is confirmed in place and resolves that issue. However, bare `simp` closes 4 of 7 levels (L02, L04, L05, L06) as a one-shot tactic, and `norm_num` closes the same 4. Neither is in the DisabledTactic list. This is a **P0 exploitability problem**. The boss (L07) is NOT exploitable by `simp` or `norm_num` (parts 1 and 2 resist), which is good. The build also warns that `Finset.mem_range` is used but never introduced as a `NewTheorem`. No new P0 issues beyond the `simp`/`norm_num` exploit.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good concrete exercise of filter, image, powerset, product. Powerset/product are "preview" (intro only, no retrieval). Acceptable for example world. |
| 2. Granularity fit | 3 | Each level has a clear dominant lesson. No overfine or overbroad levels. The boss is genuine integration (not gauntlet). |
| 3. Proof-move teaching | 3 | `ext` + membership reasoning well exercised. `rintro` pattern first-contact in L04. Witness-providing for image well coached. |
| 4. Inventory design | 3 | `rintro`/`ring` now properly declared (R1 fix confirmed). `Finset.range`, `Finset.powerset`, `Finset.product` introduced with docs. One gap: `Finset.mem_range` used but not declared as NewTheorem. |
| 5. Hint design | 3 | Layered strategy-then-code throughout. Each level has visible + hidden hints. Boss hints reference techniques from specific prior levels. |
| 6. Progression | 3 | Clean L01 (build) -> L02 (membership) -> L03 (filter) -> L04 (image) -> L05-L06 (previews) -> L07 (boss). Support faded appropriately. |
| 7. Mathematical authenticity | 4 | Excellent concrete grounding. Tables showing filter results (L03 conclusion), squaring results (L04), powerset enumeration (L05). Good "why it matters" content. |
| 8. Paper-proof transfer | 3 | Each conclusion includes "In plain language" transfer sentences. Boss conclusion explicitly maps Lean moves to counting principles. |
| 9. Technical fit | 2 | Build passes but `simp`/`norm_num` exploit on 4/7 levels. Missing `Finset.mem_range` NewTheorem. |

**Average: 3.0** -- meets threshold but the P0 exploit drags Category 9 below 3, which is a blocking deficiency.

---

## 3. R1 Fix Verification

**R1 Issue**: `rintro` and `ring` used in L04 solution/hints but not declared via `NewTactic` or `TacticDoc`.

**Status**: FIXED. L04 now contains:
- `TacticDoc rintro` (line 113) with good documentation
- `TacticDoc ring` (line 120) with good documentation
- `NewTactic rintro ring` (line 122)

No further action needed on this item.

---

## 4. Statement Exploitability (1b)

### P0 -- bare `simp` closes 4/7 levels

| Level | `simp` | `norm_num` | `decide` (disabled) | `rfl` |
|-------|--------|-----------|---------------------|-------|
| L01 | fails | fails | closes | fails (second part) |
| L02 | **closes** | **closes** | closes | fails |
| L03 | fails | fails | closes | fails |
| L04 | **closes** | **closes** | closes | fails |
| L05 | **closes** | **closes** | closes | **closes** (P3) |
| L06 | **closes** | **closes** | closes | fails |
| L07 (Boss) | fails | fails | closes | fails |

**Impact**: A learner who discovers bare `simp` can skip L02 (membership), L04 (image -- the level that introduces `rintro` and `ring`!), L05 (powerset), and L06 (product) without learning the intended proof moves. L04 is particularly bad because it is the first-contact level for `rintro` and `ring` -- if skipped, those tactics are "learned" without any engagement.

**Fix**: Add `simp` and `norm_num` to DisabledTactic on L02, L04, L05, and L06. The intended proofs for L02 use `simp [Finset.mem_insert, Finset.mem_singleton]` which would need to be rewritten if `simp` is disabled. Options:
1. Disable bare `simp` but allow `simp only` by not adding it to DisabledTactic (note: DisabledTactic disables ALL forms of a tactic, including `simp only`). So this approach won't work.
2. Restructure the intended proofs for L02 to use `rw [Finset.mem_insert]` + `left; rfl` or similar explicit reasoning, then add `simp` to DisabledTactic.
3. Accept the `simp` exploit on L02 as P2 (since the learner must already know `simp` is available, and the level's main lesson is membership reasoning which is still taught via text). Focus the disable on L04 (critical because `rintro`/`ring` first-contact), L05, L06.

**Recommended**: Add `simp norm_num` to DisabledTactic on L04, L05, L06. For L02, the intended proof uses `simp [...]`, so either restructure the proof or accept the exploit as P2. For L05, `rfl` also closes the goal (P3, cannot disable `rfl`); accept this since the learner still reads the intro explaining `card_powerset`.

### P3 -- `rfl` on L05

`rfl` closes L05 (`({1, 2, 3} : Finset Nat).powerset.card = 8`) directly without the intended `rw [Finset.card_powerset]` step. This is because the powerset card computes definitionally. Cannot disable `rfl`. The pedagogical cost is low: the learner still sees the intro about `card_powerset` and the conclusion. Accept as P3.

---

## 5. Coverage Gaps

### 5a. Covered well
- `Finset.range` definition (I in L01, with doc)
- Literal vs insert vs range+image construction (I in L01)
- Membership/non-membership of concrete finsets (R in L02, from prior worlds)
- `Finset.filter` on concrete data (R in L03)
- `Finset.image` on concrete data (R in L04, with witness reasoning)
- `rintro` for destructuring existentials (I in L04)
- `ring` for arithmetic (I in L04)
- `Finset.powerset` (I in L05, preview)
- `Finset.card_powerset` (I in L05)
- `Finset.product` (I in L06, preview)
- `Finset.mem_product` and `Finset.card_product` (I in L06)
- Integration of all operations in boss (G in L07)

### 5b. Gaps

| Gap | Severity | Description |
|-----|----------|-------------|
| `Finset.mem_range` used in L01 proof but not declared as `NewTheorem` | P2 | Build warns: "No world introducing Finset.mem_range, but required by FinsetExploration". Should add `TheoremDoc` + `NewTheorem` in L01. |
| No retrieval of `rintro` after L04 | P2 | `rintro` is introduced in L04 but the boss's Part 2 (image cardinality) uses it again. This is retrieval in the boss, which is acceptable for an example world. |
| Powerset/product are preview-only | P3 | These are introduced but have no supported practice or retrieval within this world. Acceptable because the plan explicitly marks them as "preview" for later worlds. |

---

## 6. Granularity Defects

No granularity defects found. Each level has a single clear dominant lesson:
- L01: Construction equivalences (3 representations of the same finset)
- L02: Membership and non-membership checking
- L03: Concrete filter computation
- L04: Concrete image computation (with `rintro`/`ring`)
- L05: Powerset cardinality (preview)
- L06: Product membership and cardinality (preview)
- L07: Boss integration of all operations

The boss (L07) is genuine integration, not a gauntlet: the four parts use distinct techniques and the planning challenge is "which technique for which part." No split needed.

---

## 7. Interactive Proof Quality (1c)

| Level | Assessment | Notes |
|-------|-----------|-------|
| L01 | OK | `constructor` -> `rfl` (Part 1) -> `ext x` -> `simp only [...]` -> `constructor` -> `rintro`/case splits (Part 2). Each step gives visible feedback. |
| L02 | OK | `constructor` -> `simp [mem_insert, mem_singleton]` for each part. Short and interactive. |
| L03 | OK | `ext x` -> `simp only [...]` -> `omega`. Clean 3-step proof. |
| L04 | OK | `ext x` -> `simp only [...]` -> `constructor` -> `rintro`/case analysis. Each step visible. |
| L05 | OK | `rw [Finset.card_powerset]` -> `rfl`. Two steps, each informative. |
| L06 | OK | `constructor` -> `rw [Finset.mem_product]` -> `constructor` -> `simp [...]` (x2) for Part 1. `rw [Finset.card_product]` for Part 2. Clean. |
| L07 | OK | `refine ⟨?_, ?_, ?_, ?_⟩` splits into 4 goals. Each goal reuses a technique from a prior level. The `have` + `rw` pattern in Parts 1-2 gives intermediate feedback. |

No interactive proof quality issues found.

---

## 8. Learner Simulation

### Attentive novice

**L01**: The intro clearly explains three construction methods. Part 1 (`rfl`) is a pleasant surprise -- "they're definitionally the same!" Part 2 is harder: `ext x` is a new move in this context (reducing finset equality to membership). The hints guide well. **First likely stuck point**: After `ext x`, the novice may not know which `simp only` lemmas to use. The hint gives the exact list. **Rescue quality**: Good, hints layer from strategy to code.

**L02**: Smooth retrieval exercise. The novice has seen `simp [mem_insert, mem_singleton]` in W8 and applies it here. The non-membership part is conceptually interesting (check all disjuncts are false). **Most likely wrong move**: Trying `exact` instead of `simp` for membership. Hints catch this.

**L03**: `ext` + `simp only` + `omega` is becoming a pattern. The novice may need the hint for `omega` if they haven't seen it close membership arithmetic before. But `omega` was taught in prior worlds. Good practice.

**L04**: **First likely stuck point**: The `rintro ⟨a, ha, rfl⟩` pattern is new. The intro doesn't explain `rintro` (the TacticDoc does, and it's revealed via NewTactic). The novice needs to discover this pattern from the hints. The layered hints guide well: strategy hint first ("Extract the witness"), then code hint (`rintro ⟨a, ha, rfl⟩`). The backward direction (`exact ⟨_, by simp, by ring⟩`) is a complex expression -- but each case is one line and the hint shows the pattern. **Most likely wrong move**: Trying `use` instead of `rintro` for the forward direction (but `use` is for constructing existentials, not destructuring them; the novice may be confused). The hint rescues.

**L05**: Easy level after the intro explains `card_powerset`. The novice does `rw [Finset.card_powerset]; rfl`. Or just `rfl` (which also works). The learning is in the intro text.

**L06**: Two-part conjunction. The novice practices `rw [Finset.mem_product]` (new lemma) and `rw [Finset.card_product]`. Both are straightforward applications. Hints guide well.

**L07 (Boss)**: The `refine ⟨?_, ?_, ?_, ?_⟩` splitting technique is well-hinted. Each of the four parts maps to a prior level. **First likely stuck point**: Part 1 (filter cardinality) requires a `have` to identify the filter, then `rw` and `rfl`. The novice may not think to use `have`. The hint suggests it. **Second stuck point**: Part 2 (image cardinality) requires replaying the L04 proof inside a `have`. This is long but familiar. The boss is coaching-dependent for weaker novices but testing for stronger ones. Acceptable for an example world boss.

### Experienced Lean user

**L02, L04, L05, L06**: Bare `simp` closes all four. The experienced user skips them in seconds. This undermines the world's purpose. **With `simp` disabled** (recommended fix), the experienced user would need to do the explicit steps but would find them straightforward.

**L01**: Not exploitable by `simp`. The experienced user does `constructor; rfl; ext x; simp only [...]; constructor; · rintro ...; · rintro ...` fluently. Minor friction: the `rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩` line is efficient but requires knowing the `<;>` combinator. No alias gaps.

**L03**: Not exploitable by `simp`. The experienced user does `ext x; simp only [...]; omega` quickly. Clean.

**L07 (Boss)**: Not exploitable. Parts 1-2 require genuine work. Parts 3-4 are one-liners (`rw [card_powerset]; rfl` and `rw [card_product]`). The experienced user appreciates the integration structure. No inventory clutter complaints.

**Alias gaps**: None. `Finset.mem_product`, `Finset.card_product`, `Finset.card_powerset` are all properly documented.

**Inventory clutter**: Minimal. New items introduced are well-chosen and documented.

---

## 9. Boss Integrity (L07)

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | GOOD | Part 1 uses L03 technique (ext + simp + omega). Part 2 uses L04 technique (ext + simp + rintro + case split). Part 3 uses L05 (card_powerset). Part 4 uses L06 (card_product). All seeded. |
| Closure quality | GOOD | Each technique was introduced AND practiced before the boss. |
| Integration quality | GOOD | The four parts require different techniques; the planning challenge is "which technique applies to which part." Not a gauntlet -- the parts interact through the shared context of "operations on finsets." |
| Surprise burden | LOW | No new proof moves. The `have h : ... := by ...` pattern in Parts 1-2 is the only possibly unfamiliar move, but `have` is a basic tactic from NNG4. |
| Can learner explain the proof? | YES | The conclusion explicitly maps each part to the relevant counting principle. Transfer moment is strong. |

**Boss verdict**: Well-designed. No lottery elements. Good integration quality. The boss passes all required checks.

---

## 10. Course-Role Sanity

The world is cast as an **example world** and behaves correctly as one:
- It does not introduce new abstract theory (except preview items powerset/product which are appropriate for an example world).
- It exercises existing theory (filter, image, membership) on concrete data.
- The boss integrates concrete skills, not abstract ones.
- Transfer moments are concrete ("in plain language" statements throughout).

No role misfits.

---

## 11. Technical Risks

| Risk | Severity | Details |
|------|----------|---------|
| `simp` not disabled | P0 | Closes L02, L04, L05, L06 as one-shot. See Section 4. |
| `norm_num` not disabled | P0 | Closes same 4 levels. See Section 4. |
| Missing `Finset.mem_range` NewTheorem | P2 | Used in L01 `simp only` call and mentioned in `Finset.range` DefinitionDoc. Build warns "No world introducing Finset.mem_range". Add `TheoremDoc` + `NewTheorem` in L01. |
| Missing TacticDoc for `aesop`, `simp_all` in L07 | P3 | Pre-existing upstream pattern. Build warns but these are disabled tactics with docs defined in earlier worlds. The warn is about the GameServer re-checking. Not blocking. |
| `rfl` closes L05 | P3 | Cannot disable `rfl`. Learner still reads intro. Accept. |

---

## 12. Ranked Patch List

| # | Severity | Level(s) | Issue | Recommended Fix |
|---|----------|----------|-------|-----------------|
| 1 | P0 | L04 | `simp` closes entire goal, bypassing `rintro`/`ring` first-contact | Add `simp norm_num` to DisabledTactic. Restructure intended proof: replace `rcases ha with rfl \| rfl \| rfl \| rfl \| rfl <;> simp` with `rcases ha with rfl \| rfl \| rfl \| rfl \| rfl <;> ring` (or `<;> norm_num` if `norm_num` is kept). Also in backward direction, replace `by simp` with `by rw [Finset.mem_insert]; left; rfl` or similar. |
| 2 | P0 | L05 | `simp` and `norm_num` close entire goal | Add `simp norm_num` to DisabledTactic. Intended proof (`rw [Finset.card_powerset]; rfl`) does not use `simp` or `norm_num`, so no proof restructuring needed. |
| 3 | P0 | L06 | `simp` and `norm_num` close entire goal | Add `simp norm_num` to DisabledTactic. Restructure membership subgoal proofs from `simp [Finset.mem_insert, Finset.mem_singleton]` to explicit `rw [Finset.mem_insert]; left; rfl` / `rw [Finset.mem_insert]; right; rw [Finset.mem_singleton]` etc. |
| 4 | P0 | L02 | `simp` and `norm_num` close entire goal | Add `simp norm_num` to DisabledTactic. Restructure intended proof from `simp [Finset.mem_insert, Finset.mem_singleton]` to explicit membership reasoning (e.g., `rw [Finset.mem_insert]; right; rw [Finset.mem_insert]; right; rw [Finset.mem_insert]; left; rfl` for the `3 ∈ ...` part, and intro + rewrite chain for the `6 ∉ ...` part). |
| 5 | P2 | L01 | `Finset.mem_range` used in `simp only` but not declared | Add `TheoremDoc Finset.mem_range as "Finset.mem_range" in "Finset"` and add `Finset.mem_range` to the `NewTheorem` line (or add a new `NewTheorem Finset.mem_range` line, but note: only one `NewTheorem` per level -- combine with any existing). Currently L01 has `NewDefinition Finset.range` only, so add `NewTheorem Finset.mem_range`. |

---

## 13. What to Playtest After Patching

After implementing patches 1-5:

1. **L02, L04, L05, L06 exploitability**: Verify `simp`, `norm_num`, `simp_all` all fail on these levels after DisabledTactic changes.
2. **L02, L04, L06 intended proofs still compile**: After restructuring away from `simp`, verify the new proof steps work and produce sensible intermediate goals.
3. **L04 hint consistency**: After proof restructuring, verify hints still match the intended proof steps. The existing hints reference `simp` in some places.
4. **L01 inventory**: Verify `Finset.mem_range` appears in learner's theorem panel after L01.
5. **L07 Boss**: Verify the boss still compiles and the intended proof still works (it should, since the boss's `simp` calls are `simp only` with arguments and in subgoal position, not bare `simp`).
