# Playtest Audit: W1 FinIntro ("What is Fin n?")

Auditor: lean4game-playtest-auditor
Date: 2026-03-14
World files: L01_WhatIsFin through L12_Boss (12 levels)
Prior reviews: W1_FinIntro_enrichment.md (R1), W1_FinIntro_enrichment_r2.md (R2)
Build status: **Compiles** (8113 jobs, no errors)

---

## 1. Overall verdict

**CONDITIONAL PASS -- requires fixes before shipping.**

The world is well-structured and covers the definition of `Fin n` thoroughly. The prose is excellent. However, there are several blocking and high-severity defects:

- **P0**: The boss (L12) introduces `congr_arg` as a new proof move at the integration point -- a direct violation of "bosses integrate, never introduce."
- **P0**: The boss (L12) is exploitable via `exact Fin.castSucc_ne_last i` -- a one-shot library lemma that bypasses the intended lesson entirely, and is not disabled.
- **P1**: Three consecutive `rfl` levels (L08-L10) create a dead zone with no genuine proof work, followed immediately by a `rfl` level (L11), making four `rfl` or near-`rfl` levels in a row before the boss.
- **P1**: Zero inventory documentation -- no `TacticDoc`, `TheoremDoc`, or `DefinitionDoc` entries exist anywhere in the project. Every `NewTactic`, `NewTheorem`, and `NewDefinition` item is undocumented in the inventory panel.
- **P1**: L01 (`Fin 5 := by ...`) has an unconstrained return type -- `exact 0`, `exact default`, `exact ⟨0, by omega⟩` all work without the learner choosing the value `3` as intended.

The world passes on mathematical content and arc design. It fails on exploitability, boss integrity, and inventory documentation.

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Core items (M1-M3, N8) are introduced. Closure is thin -- many items only reach I or S. |
| 2. Granularity fit | 2 | Four consecutive `rfl`/trivial levels (L08-L11) break the flow. L03/L04 are tight but good. |
| 3. Proof-move teaching | 2 | `intro` + contradiction (L05, L07, L12) is taught. `ext` is taught. But `congr_arg` appears untaught in the boss. The `rfl` stretch teaches no proof moves. |
| 4. Inventory design | 1 | No documentation entries at all. `NewTactic` in L01 dumps 9 tactics at once. `congr_arg` as `NewTheorem` only in the boss. |
| 5. Hint design / recoverability | 3 | Hints are well-placed and layered in most levels. L07 has a hidden hint. Boss hints guide step-by-step. No Branch alternatives. |
| 6. Worked example -> practice -> transfer -> boss | 2 | The boss integrates castSucc + last but not ext, succ, or elim0. The navigation trio (L08-L10) has no practice -- only observation. |
| 7. Mathematical authenticity | 3 | Prose is excellent. Transfer paragraphs in L05, L06, L12 connect to paper proofs. Fin 0/Fin 1 boundary cases are well-motivated. Motivation for *why* Fin n matters is weak (L01 intro). |
| 8. Paper-proof transfer | 3 | L12 conclusion has a detailed tactic-to-sentence mapping. L05 and L06 have "in plain language" sections. Transfer is present but limited to conclusions. |
| 9. Technical fit / maintainability | 3 | Builds cleanly. Dependencies are correct. World size (12 levels) is reasonable. No hidden import issues. |

**Average: 2.4** -- Below the "good" threshold of 3.0.
**Categories below 2: one** (Inventory design at 1).
**Red flags triggered**: Missing docs for newly unlocked items (all items). Boss depends on untaught micro-skill (congr_arg). Major definition (`Fin n`) never exercised on concrete example after L01 (construction skill atrophies -- noted by R2 #3).

---

## 3. Technical sanity

### 3a. Build / import issues
- **None.** The project builds with 8113 jobs, no errors. Only warnings are i18n translations (expected).

### 3b. Hidden alias opportunities
- `Fin.elim0` is introduced as `NewTheorem` in L05 after the learner discovers the proof from primitives. This is correct. However, `finZeroElim` is mentioned in prose but not in `NewTheorem` -- potential confusion if learner searches for it.
- `↑i` (coercion) is explained in L02 prose. No hidden alias concern.

### 3c. Statement exploitability

| Level | Statement | Exploit | Severity |
|-------|-----------|---------|----------|
| L01 | `Fin 5 := by` | `exact 0`, `exact default`, `exact ⟨0, by omega⟩` (any value works) | **P1** -- learner can pass without choosing `3` as intended. The lesson "construct with value and proof" still works with any value, but the introduction specifically coaches `⟨3, by omega⟩`. A learner who types `exact 0` learns nothing about `Fin.mk`. |
| L02 | `i.val < 5` | Only `exact i.isLt`. Not exploitable. | OK |
| L03 | `Fin.mk 2 h₁ = Fin.mk 2 h₂` | `rfl` works (proof irrelevance). | **P2** -- `rfl` closes without `ext`. The introduction teaches `ext` -> `rfl`, but the learner can skip `ext` entirely. Not blocking because `rfl` demonstrates the same concept (proofs don't matter), but the `ext` tactic gets zero practice here. |
| L04 | `Fin.mk i.val i.isLt = i` | `rfl` works (eta for structures). | **P2** -- same as L03. `ext` is the intended path but `rfl` bypasses it. |
| L05 | `(h : Fin 0) → False` | `exact h.elim0`, `exact Fin.elim0 h`, `exact absurd h.isLt (by omega)`. | OK -- all valid alternatives engage with the concept. |
| L06 | `(a b : Fin 1) → a = b` | `omega` closes in one step. | **P2** -- `omega` bypasses `ext`. Acceptable because `omega` understands Fin equality, but the learner may never type `ext`. |
| L07 | `(0 : Fin 3) ≠ (1 : Fin 3)` | `omega` (intended), `decide`. | OK -- both paths teach the concept. |
| L08 | `(Fin.last 4).val = 4` | `rfl` (intended). | OK |
| L09 | `(Fin.castSucc i).val = i.val` | `rfl` (intended). | OK |
| L10 | `(Fin.succ i).val = i.val + 1` | `rfl` (intended). | OK |
| L11 | `(Fin.last 3).val + 1 = 4` | `rfl` (intended). | OK |
| L12 | `Fin.castSucc i ≠ Fin.last 4` | **`exact Fin.castSucc_ne_last i`** -- one-shot library lemma. Also `exact ne_of_lt (Fin.castSucc_lt_last i)`. Also `simp [Fin.ext_iff]; omega`. | **P0** -- the boss can be solved with a single `exact` that completely bypasses the intended proof of `intro h; have hv := congr_arg Fin.val h; omega`. The library lemma `Fin.castSucc_ne_last` is not disabled. This is a blocking defect. |

### 3d. Interactive proof quality

| Level | Intended proof | Issue | Severity |
|-------|---------------|-------|----------|
| L01 | `exact ⟨3, by omega⟩` | This is a one-liner that requires typing angle brackets + `by omega` as a nested expression. No intermediate feedback until the entire expression is correct. | **P2** -- The learner must get the whole expression right before seeing any goal change. However, for a first level, this is conventional (NNG4 does similar). Acceptable but not ideal. |
| L03 | `ext; rfl` | Two clean steps. | OK |
| L04 | `ext; rfl` | Two clean steps. | OK |
| L05 | `have h_lt := h.isLt; omega` | Two clean steps. Excellent -- intermediate feedback after `have`. | OK |
| L12 | `intro h; have hv : i.val = 4 := congr_arg Fin.val h; omega` | The `have` step requires typing `have hv : i.val = 4 := congr_arg Fin.val h` -- a long expression with a type annotation and an explicit term. No feedback until the entire line is correct. | **P1** -- This is a significant interactive-quality issue. The learner must compose `congr_arg Fin.val h` (an unfamiliar function application) with a type annotation, all in one go. A `have` step with `:= by exact congr_arg Fin.val h` would at least let them enter tactic mode, but even that requires knowing `congr_arg`. |

---

## 4. Coverage sanity

### 4a. Core items coverage states

| Item | Axis | Importance | I | S | R | G | T | W | Notes |
|------|------|-----------|---|---|---|---|---|---|-------|
| M1: `Fin n` as subtype | MATH | core | L01 | L02-L06 | -- | L12 | -- | -- | Never retrieved unsupported. |
| M2: `Fin.val`, constructors, navigation | MATH | core | L01-L02 | L03-L04, L08-L10 | -- | L12 | -- | -- | Practice is all `rfl`. |
| M3: Boundary cases (Fin 0, Fin 1) | MATH | core | L05, L06 | -- | -- | -- | -- | L05 (C5) | Introduced but never revisited. |
| N8: Coercion `↑` / `.val` | NOTATION | core | L02 | L08-L11 | -- | L12 | -- | -- | Explained in prose. Never causes confusion because all levels use `.val` explicitly. |
| C5: Fin 0 empty, not singleton | MISCONCEPTION | core | L05 | L06 | -- | -- | -- | L05 | Well-handled. |
| C6: Zero-indexing | MISCONCEPTION | core | L11 | -- | -- | -- | -- | L11 | Addressed in L11 but with a trivial (`rfl`) statement. |
| `ext` tactic | LEAN | core | L03 | L04, L06 | -- | NOT in boss | -- | -- | **Gap**: taught but not tested in boss. |
| `omega` tactic | LEAN | supporting | L01 | L05, L06, L07 | -- | L12 | -- | -- | Well-covered. |
| `congr_arg` | LEAN/MOVE | supporting | **L12 (boss!)** | -- | -- | -- | -- | -- | **Gap**: first introduction is in the boss. No prior contact. |
| `Fin.elim0` | MATH | supporting | L05 | -- | -- | -- | -- | -- | Mentioned in conclusion as shortcut. |
| `Fin.castSucc` | MATH | core (for boss) | L09 | -- | -- | L12 | -- | -- | Introduced with `rfl`, then immediately used in boss. No intermediate practice. |
| `Fin.last` | MATH | core (for boss) | L08 | L11 | -- | L12 | -- | -- | Same pattern as castSucc. |
| `Fin.succ` | MATH | supporting | L10 | -- | -- | NOT in boss | -- | -- | Introduced but never used again. |

### 4b. Coverage gaps

1. **`congr_arg` has zero coverage before the boss.** It appears only in L12 as `NewTheorem congr_arg`. The boss uses it as a proof move. This is a hidden prerequisite leak (failure taxonomy #1). **Blocking.**

2. **`ext` is taught in L03-L06 but absent from the boss.** The boss could use `ext` (e.g., if the statement required proving equality rather than inequality), but the current boss statement does not exercise it. The world's most distinctive proof move (`ext`) has no integration moment.

3. **`Fin.succ` (L10) is introduced but never used.** It does not appear in the boss or in any subsequent level within this world. The learner learns what `Fin.succ` does but has no reason to remember it. (W2 may reuse it, which is acceptable, but within W1 the item has zero closure beyond introduction.)

4. **No concrete example of constructing a `Fin` element after L01.** The construction skill (`Fin.mk` / angle brackets + proof) atrophies. (Flagged by R2 #3.)

5. **`Fin.ext_iff` is mentioned in prose (L03) but not in inventory.** (Flagged by R2 #8.)

### 4c. Proof moves taught

| Move | Where taught | Where practiced | Where integrated | Notes |
|------|-------------|----------------|-----------------|-------|
| Subtype extensionality (`ext`) | L03 | L04, L06 | -- (not in boss) | Gap: no integration |
| Extract contradiction from impossible bound | L05 | L07 (similar pattern) | L12 (via omega) | OK |
| Intro + contradiction for `≠` | L07 | -- | L12 | Thin practice |
| Construct a Fin element | L01 | -- | -- | No retrieval after L01 |
| Use `.isLt` to get bound proof | L02 | L05 | L12 | OK |
| `congr_arg` for congruence | -- | -- | L12 | **Not taught** |

### 4d. Transfer

Transfer moments appear in:
- L05 conclusion: "If someone claims to have a natural number less than zero..."
- L06 conclusion: "The only natural number less than 1 is 0..."
- L07 conclusion: mental model "Fin n is the set {0, ..., n-1}"
- L12 conclusion: detailed tactic-to-sentence mapping

Transfer is present and good in quality but limited to conclusions. No level's *statement* is a transfer exercise (e.g., "state in words..."). This is acceptable for W1 (lecture world), but the world plan calls for a transfer moment at the boss, which is delivered.

### 4e. Examples / concretization

- L01: constructs an element of `Fin 5` (concrete)
- L05: `Fin 0` boundary (concrete)
- L06: `Fin 1` boundary (concrete)
- L07: `Fin 3` elements are distinct (concrete)
- L08: `Fin.last 4` value (concrete)

The world has reasonable concretization. The main gap is that `Fin n` for general `n` is never exercised -- all levels use specific small values. This is fine for W1 (the learner is building intuition), but it means generalization to arbitrary `n` is deferred entirely to later worlds.

---

## 5. Granularity sanity

### 5a. Level-by-level granularity check

| Level | Dominant lesson | Too broad? | Too fine? | Notes |
|-------|----------------|-----------|----------|-------|
| L01 | Construct Fin 5 | No | No | Good first contact. |
| L02 | Extract `.val` and `.isLt` | No | No | Clean. One lesson: extraction. |
| L03 | Subtype extensionality | No | Borderline | `ext; rfl` is very short. But the concept is important. OK. |
| L04 | Round-trip mk/val | No | **Yes** | `ext; rfl` again. Same proof shape as L03 with a different semantic point (round-trip). The learner might wonder why this is a separate level when the proof is identical to L03. However, the pedagogical point (constructor/destructor inverses) is distinct. Marginal. |
| L05 | Fin 0 is empty | No | No | Excellent. Two-step proof with genuine reasoning. |
| L06 | Fin 1 is singleton | No | No | `ext; omega`. Combines `ext` with arithmetic. |
| L07 | Distinct elements | No | Borderline | One-tactic proof (`omega`). But concretization is the lesson, not proof complexity. OK. |
| L08 | Fin.last value | No | **Yes** | `rfl`. No proof work. Pure definition observation. |
| L09 | castSucc preserves value | No | **Yes** | `rfl`. Same as L08. |
| L10 | Fin.succ increments value | No | **Yes** | `rfl`. Three in a row. |
| L11 | Zero-indexing misconception | No | **Yes** | `rfl`. Four `rfl`-grade levels in a row (L08-L11). |
| L12 | Boss: castSucc ≠ last | No | No | Good integration level. But see boss analysis below. |

### 5b. Dead zone: L08-L11

Four consecutive levels (L08, L09, L10, L11) are all solved by `rfl`. The learner reads an introduction, types `rfl`, reads a conclusion, and advances. This is a **dead zone** where the proof work provides zero engagement.

The enrichment reviewer (R2 #1) flagged this. The remedy is to make at least one or two of these levels require a multi-step proof that exercises the navigation function in combination with prior skills.

**Severity: P1.** The dead zone is not blocking, but it degrades the learning experience and leaves the learner unprepared for the boss.

### 5c. World center of gravity

The world's center is "what is `Fin n` and how do you navigate it." This is coherent. The 12 levels cover:
- Definition (L01-L04): construction, extraction, extensionality, round-trip
- Boundary cases (L05-L06): empty and singleton
- Concretization (L07): distinct elements
- Navigation (L08-L10): last, castSucc, succ
- Misconception (L11): zero-indexing
- Boss (L12): integration

This is a well-organized arc. The center is stable. No splitting is needed.

### 5d. Boss seeding

The boss requires:
1. `intro h` -- practiced in L07 (intro for ≠ goals)
2. `have hv : ... := congr_arg Fin.val h` -- **NOT seeded**. `congr_arg` is new.
3. `omega` -- practiced in L05, L06, L07

The boss is **not fully seeded**. The `congr_arg` step is the novel element. Even if we remove `congr_arg` (by changing the proof path), the boss still requires extracting a value-level consequence from a Fin-level equality, which has not been practiced in any prior level.

---

## 6. Learner simulation

### 6a. Attentive novice

**Profile**: Completed NNG4. Comfortable with `rw`, `exact`, `apply`, `intro`, `cases`, `omega`. Reads introductions carefully.

**L01**: Reads the introduction, understands the structure definition. Types `exact ⟨3, by omega⟩`. Succeeds. Learns that `Fin 5` is a pair. **Risk**: types `exact 0` and it works. Wonders why the introduction talked about `⟨3, by omega⟩` when `0` worked. Mild confusion but not stuck.

**L02**: Types `exact i.isLt`. Quick win. Understands extraction.

**L03**: Reads about extensionality. Types `ext`. Sees goal change to `2 = 2`. Types `rfl`. Clean. **Risk**: types `rfl` directly (without `ext`) and it works. Wonders what `ext` was for.

**L04**: Recognizes the same pattern. Types `ext; rfl`. Quick win.

**L05**: This is the first level with genuine reasoning. Reads the plan: extract `h.isLt`, then `omega`. Types `have h_lt := h.isLt`. Sees the new hypothesis. Types `omega`. Succeeds. **This is the best level in the world** -- the learner discovers the proof from principles, not from memorizing a function.

**L06**: Types `ext; omega`. Quick.

**L07**: Types `omega`. Quick. Reads conclusion about Fin n = {0, ..., n-1}.

**L08-L11**: Four `rfl` levels. **The novice's engagement drops.** They read the introductions (which are well-written) but the proof work is trivial. By L10 or L11, they may be skimming introductions. This is a problem because L09 (castSucc) and L10 (succ) contain important structural information that the learner needs for the boss.

**L12 (Boss)**: The novice reads the introduction. It says to use `intro h`, then `have hv : i.val = 4 := congr_arg Fin.val h`, then `omega`.

**First likely stuck point**: The `have hv : i.val = 4 := congr_arg Fin.val h` step. The novice has never seen `congr_arg`. The introduction explains it, and the hints guide to it, but the novice must type a complex expression correctly on first try. This is a **surprise burden**: the boss introduces a new tool (`congr_arg`) while simultaneously requiring integration.

**Most likely wrong move**: The novice tries `omega` after `intro h` (since `omega` has solved every arithmetic problem so far). It fails. Then tries `ext` (since they know `ext` for `Fin` equality). It fails (the goal is `False`, not an equality). Then reads the hint and tries the `congr_arg` line. If they mistype it (wrong argument order, missing type annotation), they get a confusing error.

**Do hints rescue well?** Yes, the hints guide step-by-step. But the novice must type a term-mode expression they have never practiced, which is uncomfortable. If they follow the hints exactly, they will succeed, but it feels like copying rather than understanding.

**Is the level's lesson legible?** The *intended* lesson (castSucc and last have disjoint images) is legible from the introduction and conclusion. But the *proof* lesson (use congr_arg to extract value-level consequences) is opaque because the tool is new.

### 6b. Experienced Lean user

**Profile**: Has used Lean 4 / mathlib. Knows `simp`, `exact?`, `omega`, `decide`.

**L01-L06**: Breezes through. May use shortcuts (`rfl` for L03/L04, `omega` for L06).

**L07**: Types `decide` or `omega`. Both work.

**L08-L11**: Types `rfl` four times. May feel bored but reads the conclusions for exposition.

**L12**: **Immediately types `exact Fin.castSucc_ne_last i` or `exact ne_of_lt (Fin.castSucc_lt_last i)`.** Bypasses the entire intended proof. Learns nothing from the boss. This is the **worst-case exploit**: the experienced user's natural approach completely avoids the pedagogical content.

**Avoidable friction**: None significant. The experienced user will not be frustrated -- the levels are easy and well-documented.

**Alias gaps**: `finZeroElim` is mentioned in L05 prose but not available as an alias in the inventory. The experienced user who remembers this name from prior work cannot use it as a shortcut. Minor.

**Inventory clutter**: L01 dumps 9 tactics at once (`omega exact intro have assumption apply rw constructor use cases`). The experienced user will not be confused, but the inventory panel is cluttered from the start. Most of these are NNG4 baseline tactics and should not need re-introduction. The issue is more about novice confusion than expert friction.

---

## 7. Boss integrity check (L12)

### Seeded subskills

| Subskill | Seeded? | Where? |
|----------|---------|--------|
| `intro h` for ≠ goals | Yes | L07 (intro h for Fin literal inequality) |
| `congr_arg Fin.val h` | **No** | First appearance in L12 |
| `omega` for contradiction | Yes | L05, L06, L07 |
| Understanding castSucc preserves value | Partially | L09 (`rfl` level -- observed but not practiced) |
| Understanding last has value n | Partially | L08 (`rfl` level -- observed but not practiced) |

**Verdict**: The boss has an **unseeded subskill** (`congr_arg`). This is a lottery boss defect (failure taxonomy #9). The `congr_arg` step is the novel integration challenge that should have been taught earlier.

### Closure quality
The boss uses castSucc and last, which are introduced in L08-L09. But the learner has only observed these via `rfl` -- never used them in a proof that requires reasoning. The boss's proof relies on definitional reduction (`(Fin.castSucc i).val = i.val` by definition), which the learner knows from L09 but has never needed to invoke in a non-trivial context.

### Integration quality
The boss combines: intro, have with term-mode expression, omega. It does **not** integrate: ext (L03-L06), Fin.succ (L10), or boundary case reasoning (L05-L06). This means only half the world's content is tested at the integration level.

### Surprise burden
`congr_arg` is a surprise. The type annotation `have hv : i.val = 4 := ...` adds a syntax burden (type-annotated `have` with `:=` term) that is beyond what was practiced.

### Can the learner explain why the proof works?
Yes -- the L12 conclusion provides an excellent tactic-to-sentence translation. The *mathematical* reasoning is clear (castSucc has value < n, last has value n, contradiction). The *Lean* reasoning is less clear because `congr_arg` is unfamiliar.

---

## 8. Course-role sanity

| Level | Intended role | Actual role | Miscast? |
|-------|--------------|-------------|----------|
| L01 | First contact (Fin, Fin.mk) | First contact | No |
| L02 | First contact (Fin.val, isLt) | First contact | No |
| L03 | First contact (ext, subtype extensionality) | First contact | No |
| L04 | Supported practice (round-trip) | Supported practice | No |
| L05 | First contact (Fin 0) + misconception | First contact + worked example | No |
| L06 | Supported practice (Fin 1, ext + omega) | Supported practice | No |
| L07 | Concretization / example | Example | No |
| L08 | First contact (Fin.last) | **Observation** | **Marginal** -- this is labeled as a "first contact" but it teaches nothing the learner must discover through proof work. It is more of a definition display. |
| L09 | First contact (castSucc) | **Observation** | **Marginal** -- same issue as L08. |
| L10 | First contact (Fin.succ) | **Observation** | **Marginal** -- same. |
| L11 | Misconception confrontation (C6) | **Observation** | **Yes** -- a misconception level should force the learner to confront the error through proof work. This level's `rfl` proof does not confront anything. |
| L12 | Boss | Boss (with caveats) | **Yes** -- introduces new material (congr_arg), making it partially a first-contact level for that concept. |

---

## 9. Technical risks

1. **`Fin.castSucc_ne_last` not disabled in L12.** Any learner who uses `exact?` or knows the library will bypass the boss entirely. This undermines the world's capstone.

2. **`decide` not disabled in L07.** This is less critical because `decide` teaches the same lesson (the elements are distinct), but it bypasses the `omega` path that the hints guide toward. If W2 introduces `decide` as a new tactic, then using it in W1 without introduction creates a forward dependency.

3. **L01's `NewTactic` dumps 9 tactics.** The lean4game server's inventory DSL replaces (not appends) on each `NewTactic` call. This means L01's single `NewTactic omega exact intro ...` is the only tactic introduction for the entire world. If a subsequent level accidentally had a second `NewTactic` call, it would overwrite this list. Currently not a bug, but fragile.

4. **`Fin.coe_castSucc` is deprecated.** The introduction of L09 mentions this lemma name. The correct name is `Fin.val_castSucc`. If a learner tries `rw [Fin.coe_castSucc]`, they will get a deprecation warning. Minor, but worth updating the prose.

5. **No `Metadata.lean` file.** The world does not appear to use any scoped instances or notation, so this is not currently a problem. But it means the project has no central metadata configuration.

---

## 10. Ranked patch list

### P0 (Blocking -- must fix before shipping)

**P0-1. Disable `Fin.castSucc_ne_last` and related library shortcuts in L12.**
Add `DisabledTheorem Fin.castSucc_ne_last Fin.castSucc_lt_last ne_of_lt` (or the appropriate subset) to L12. The boss must not be solvable by a single `exact` with a library lemma.

**P0-2. Seed `congr_arg` before the boss.**
Either:
- (a) Add a level between L11 and L12 that introduces `congr_arg` on a simpler equality (e.g., "Given `h : a = b` for `a b : Fin 3`, prove `a.val = b.val` using `exact congr_arg Fin.val h`"). Then the boss integrates rather than introduces.
- (b) Change the boss proof path to avoid `congr_arg` entirely. For instance: `intro h; have hv := Fin.val_eq_val.mp h; omega` or `intro h; simp [Fin.ext_iff] at h; omega`. But these may introduce different unseeded tools.
- Recommendation: option (a) is cleaner.

### P1 (High -- should fix before shipping)

**P1-1. Break the rfl dead zone (L08-L11).**
At least two of L08-L11 should require multi-step proofs. Suggestions:
- L09 (castSucc): Change statement to "Prove `(Fin.castSucc i).val < 4` for `i : Fin 4`." Proof: `exact i.isLt` (or `have := Fin.coe_castSucc i; omega`). This combines castSucc with the bound from L02.
- L10 (Fin.succ): Change statement to "Prove `Fin.succ i ≠ 0` for `i : Fin 4`." Proof: `intro h; have := congr_arg Fin.val h; omega` (but this requires congr_arg -- only if P0-2a is implemented first). Alternative: keep the `rfl` statement but add a second goal or subpart.
- L11 (zero-indexing): Change statement to "Prove `Fin.last 3 = (3 : Fin 4)`" using `ext; rfl` or `rfl`. This is still simple but at least confronts the misconception more directly. Or change to "Prove `(Fin.last 3).val ≠ 4`" which requires `intro h; omega` (genuine reasoning).

**P1-2. Add inventory documentation.**
Every `NewTactic`, `NewTheorem`, and `NewDefinition` item needs a corresponding `TacticDoc`, `TheoremDoc`, or `DefinitionDoc` entry. At minimum, document:
- `TacticDoc omega`, `TacticDoc ext`, `TacticDoc rfl` (from L01, L03)
- `DefinitionDoc Fin`, `DefinitionDoc Fin.mk`, `DefinitionDoc Fin.val`, `DefinitionDoc Fin.isLt` (from L01, L02)
- `DefinitionDoc Fin.last`, `DefinitionDoc Fin.castSucc`, `DefinitionDoc Fin.succ` (from L08, L09, L10)
- `TheoremDoc Fin.elim0`, `TheoremDoc congr_arg` (from L05, L12)

Without these, the inventory panel shows items with no description. Learners cannot look up syntax or usage.

**P1-3. Constrain L01's statement or add a hint that guides to the intended value.**
Options:
- Change the statement to require a specific value: `∃ i : Fin 5, i.val = 3` (forces the learner to produce the specific element `3`).
- Add a `Branch` that catches `exact 0` or `exact default` and tells the learner "That works, but try constructing the element `3` specifically using `⟨3, by omega⟩` to practice the Fin.mk constructor."

**P1-4. Interactive quality of L12's `have` step.**
The `have hv : i.val = 4 := congr_arg Fin.val h` line is a term-mode expression inside a tactic proof. Consider restructuring as:
```
have hv : i.val = 4 := by exact congr_arg Fin.val h
```
Or better, if `congr_arg` is seeded beforehand (P0-2a), the learner will recognize the pattern.

### P2 (Medium -- should fix eventually)

**P2-1. L03 and L04 are exploitable by `rfl` (bypasses `ext`).**
Consider making the statements require `ext` by making the definitional equality non-trivial. For L03, use different values: `Fin.mk 2 h₁ = Fin.mk 2 h₂` is definitionally equal (proof irrelevance), so `rfl` works. This is hard to avoid for L03 specifically -- the whole point is proof irrelevance. For L04, `Fin.mk i.val i.isLt = i` is eta-reduced, so `rfl` works. Consider changing to a statement where `rfl` does not fire, e.g., involving a computation on the value side.

**P2-2. Add `Fin.ext_iff` to inventory (L03).**
Add `NewTheorem Fin.ext_iff` in L03, as suggested by R2 #8.

**P2-3. Update `Fin.coe_castSucc` reference in L09 prose.**
Change to `Fin.val_castSucc` (the non-deprecated name).

**P2-4. L01 motivation paragraph.**
Add a motivating paragraph to L01's introduction explaining *why* `Fin n` matters (R2 #9). Something like: "In mathematics, we often need to work with finite index sets. In Lean, `Fin n` is the canonical way to represent a set with exactly `n` elements -- used as indices for vectors, matrices, and finite sums."

**P2-5. Reduce L01's tactic dump.**
The `NewTactic` in L01 introduces 9 tactics at once. Most of these are NNG4 baseline. Consider moving baseline tactics to a `Welcome` level or `Metadata.lean` and only introducing `omega` as new in L01 (since it is the only genuinely new tactic for this world).

**P2-6. L06 bypass via `omega` (skipping `ext`).**
`omega` can solve L06 directly, bypassing `ext`. This means `ext` gets only two genuine practice opportunities (L03, L04) before being absent from the boss. Consider adding `DisabledTactic omega` for L06 to force the `ext; omega` path, or restructure so that `omega` alone cannot close the goal.

---

## 11. What to playtest again after patching

After implementing the P0 and P1 fixes:

1. **Re-audit L12 (boss)** with `Fin.castSucc_ne_last` disabled. Verify that no other one-shot library lemma closes the goal. Run `exact?` in the patched environment.

2. **Re-audit the new congr_arg introduction level** (if P0-2a is chosen). Verify it teaches the move cleanly and that the boss's hint path still works.

3. **Re-audit any modified `rfl` levels** (P1-1). Verify the new statements compile, the proofs are interactive-friendly, and the dominant lesson is preserved.

4. **Check inventory documentation** (P1-2). Verify that all `Doc` entries render correctly in the game server.

5. **Simulate the attentive novice through the patched L08-L12 stretch.** The current dead zone (four `rfl` levels) followed by a boss with an unseeded tool is the world's weakest stretch. After patching, this should flow: definition observation -> practice with navigation function -> congr_arg introduction -> boss integration.

6. **Re-run exploitability checks on L01** if the statement is changed (P1-3). Verify the new statement forces the intended construction.
