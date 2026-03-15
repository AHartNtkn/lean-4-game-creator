# Playtest Audit R2: W1 FinIntro ("What is Fin n?")

Auditor: lean4game-playtest-auditor (R2)
Date: 2026-03-14
World files: L01_WhatIsFin through L13_Boss (13 levels)
Prior reviews: W1_FinIntro_enrichment.md (R1), W1_FinIntro_enrichment_r2.md (R2), W1_FinIntro_playtest.md (playtest R1)
Build status: **Compiles** (8114 jobs, no errors)
Changes since R1 playtest: L01 statement rewritten; L09 statement changed; L11 statement changed; new L12_CongrArg inserted; boss renumbered to L13; `DisabledTheorem` added to boss; inventory docs added throughout.

---

## 0. Regression check: R1 P0 and P1 fixes

### P0-1 (R1): Disable `Fin.castSucc_ne_last` and related library shortcuts in boss

**Status: FIXED.**

L13_Boss now includes:
```
DisabledTheorem Fin.castSucc_ne_last Fin.castSucc_lt_last ne_of_lt
```

Verified: `exact Fin.castSucc_ne_last i`, `exact ne_of_lt (Fin.castSucc_lt_last i)`, and `(Fin.castSucc_lt_last i).ne` are all blocked. `omega` alone does not close the goal. `simp` alone does not close the goal. `decide` does not close the goal (free variable). The only known viable paths are:
- (a) `intro h; have hv : i.val = 4 := congr_arg Fin.val h; omega` (intended)
- (b) `intro h; simp [Fin.ext_iff] at h; omega`
- (c) `intro h; have hv := congr_arg Fin.val h; simp at hv; omega`

Path (b) uses `simp [Fin.ext_iff]` which is available and taught (L03). This is acceptable -- it is a legitimate alternative that still exercises understanding of value-level vs Fin-level reasoning. Path (c) is a variant of (a) without the type annotation. All three require `intro h` and extracting a value-level consequence, which is the intended lesson.

**Verdict: P0-1 is genuinely fixed. No remaining one-shot exploits.**

### P0-2 (R1): Seed `congr_arg` before the boss

**Status: FIXED.**

A new level L12_CongrArg has been inserted. It introduces `congr_arg` on a clean, low-load statement:

```
Statement (a b : Fin 3) (h : a = b) : a.val = b.val := by
  exact congr_arg Fin.val h
```

The level has:
- A clear introduction explaining `congr_arg` as "apply a function to both sides of an equality"
- The explicit connection to `ext` (converse direction)
- `TheoremDoc congr_arg` with doc entry
- `NewTheorem congr_arg`
- A hint guiding the learner to `exact congr_arg Fin.val h`
- A conclusion connecting to the upcoming boss

The boss (L13) now explicitly references L12: "You practiced `congr_arg` in the previous level!" The boss's `have hv : i.val = 4 := congr_arg Fin.val h` step reuses the exact pattern taught in L12 on harder math.

**Verdict: P0-2 is genuinely fixed. `congr_arg` is properly seeded.**

### P1-1 (R1): Break the rfl dead zone (L08-L11)

**Status: PARTIALLY FIXED.**

The original dead zone was L08-L11 (four consecutive `rfl` levels). Now:
- L08 (Fin.last): Still `rfl`. Single-step definitional observation.
- L09 (castSucc): **Changed** from `(Fin.castSucc i).val = i.val` (rfl) to `(Fin.castSucc i).val < 4` (requires `exact i.isLt`). This is an improvement -- the learner must connect castSucc's value-preserving property with the bound from L02.
- L10 (Fin.succ): Still `rfl`. Statement is `(Fin.succ i).val = i.val + 1`.
- L11 (zero-indexing): **Changed** from `(Fin.last 3).val + 1 = 4` (rfl) to `(Fin.last 3).val ≠ 4` (requires `intro h; omega`). This is a significant improvement -- the learner must confront the off-by-one via contradiction, not mere observation.

The dead zone is now L08 (rfl) followed by L09 (not rfl), L10 (rfl), L11 (not rfl). Two `rfl` levels remain but they are **non-consecutive**, which eliminates the dead-zone monotony. The learner encounters rfl, then a reasoning step, then rfl, then a reasoning step. This is acceptable pacing.

**Verdict: P1-1 is sufficiently fixed. The dead zone is broken. Two remaining `rfl` levels (L08, L10) are tolerable as definition-observation levels since they are separated by reasoning levels.**

### P1-2 (R1): Add inventory documentation

**Status: FIXED.**

Verified the following doc entries exist:
- L01: `TacticDoc` for `omega`, `exact`, `intro`, `have`, `assumption`, `apply`, `rw`, `constructor`, `use`, `cases`. `DefinitionDoc` for `Fin`, `Fin.mk`.
- L02: `DefinitionDoc` for `Fin.val`, `Fin.isLt`.
- L03: `TacticDoc` for `ext`, `rfl`. `TheoremDoc` for `Fin.ext_iff`.
- L05: `TheoremDoc` for `Fin.elim0`.
- L08: `DefinitionDoc` for `Fin.last`.
- L09: `DefinitionDoc` for `Fin.castSucc`.
- L10: `DefinitionDoc` for `Fin.succ`.
- L12: `TheoremDoc` for `congr_arg`.
- L13: `TheoremDoc` for `Fin.castSucc_ne_last`, `Fin.castSucc_lt_last`, `ne_of_lt`.

Every `NewTactic`, `NewTheorem`, and `NewDefinition` item has a corresponding doc entry. Documentation quality is good -- entries include syntax, examples, and usage context.

**Verdict: P1-2 is genuinely fixed.**

### P1-3 (R1): Constrain L01's statement

**Status: FIXED.**

L01's statement changed from `Fin 5 := by` (unconstrained return type) to `∃ i : Fin 5, i.val = 3 := by` (existential requiring the specific value 3).

Verified: `use ⟨0, by omega⟩` produces the unsolvable subgoal `0 = 3`. The learner must use `use ⟨3, by omega⟩` (or an equivalent expression producing value 3). `exact 0` and `exact default` do not work because the return type is a `Prop`, not `Fin 5`. The existential pins the intended value.

**Verdict: P1-3 is genuinely fixed.**

### P1-4 (R1): Interactive quality of L12's `have` step (now L13's)

**Status: MITIGATED.**

The `have hv : i.val = 4 := congr_arg Fin.val h` line in the boss (L13) still requires a term-mode expression. However, the same pattern was practiced in L12 (`exact congr_arg Fin.val h`), so the learner has seen the syntax before. The boss's version is harder (it adds a type annotation and wraps in `have`), but the core pattern `congr_arg Fin.val h` is familiar.

The introduction text explicitly reminds the learner of L12 and explains each piece of the `have` line. The hints are step-by-step.

**Verdict: P1-4 is adequately mitigated. The interactive quality is imperfect (the `have` line is still a term-mode expression inside a tactic proof), but the seeding in L12 makes it tolerable. Remaining concern is minor (see P2-1 below).**

---

## 1. Overall verdict

**PASS -- ship-ready with minor recommendations.**

All P0 and P1 issues from the R1 audit have been addressed. The world is now well-structured with:
- A properly constrained opening level (L01)
- Good coverage closure with `congr_arg` seeded (L12) before the boss (L13)
- The dead zone broken by L09 and L11 rework
- Complete inventory documentation
- Effective `DisabledTheorem` gating on the boss

The remaining issues are P2 (medium) -- none are blocking.

---

## 2. Rubric scores

| Category | R1 Score | R2 Score | Notes |
|----------|----------|----------|-------|
| 1. Coverage closure | 3 | 3 | Core items covered at I/S. `congr_arg` now has I (L12) + G (L13). `ext` still not in boss. |
| 2. Granularity fit | 2 | 3 | Dead zone broken. Two `rfl` levels remain but are non-consecutive. L11 now requires reasoning. |
| 3. Proof-move teaching | 2 | 3 | `congr_arg` properly taught. `intro + contradiction` practiced in L07, L11, L13. `ext` taught L03-L06. |
| 4. Inventory design | 1 | 3 | All items documented. Doc entries are well-written with syntax and examples. |
| 5. Hint design / recoverability | 3 | 3 | Hints are well-placed and step-by-step throughout. L07 has a hidden alternative. L13 has three-step guidance. |
| 6. Worked example -> practice -> transfer -> boss | 2 | 3 | L12 seeds the boss. L09/L11 now provide genuine practice for navigation concepts. Boss integrates. |
| 7. Mathematical authenticity | 3 | 3.5 | L01 motivation paragraph added ("finite index sets... matrices... finite sums"). Prose excellent throughout. |
| 8. Paper-proof transfer | 3 | 3 | L05, L06, L07, L12, L13 all have transfer paragraphs. Boss conclusion has tactic-to-sentence mapping. |
| 9. Technical fit / maintainability | 3 | 3.5 | Builds cleanly. Dependencies correct. DisabledTheorem properly applied. 13 levels is good size. |

**Average: 3.1** -- Above the "good" threshold of 3.0.
**Categories below 2: none.**
**Red flags triggered: none.**

---

## 3. Technical sanity

### 3a. Build / import issues
- **None.** Project builds with 8114 jobs, no errors. Only warnings are i18n translations (expected).
- World file `FinIntro.lean` correctly imports all 13 levels in order.

### 3b. Inventory DSL correctness
- L01 has a single `NewTactic` call with 10 tactics and a single `NewDefinition` with 2 definitions. Correct -- no overwrite risk.
- L03 has `NewTactic ext rfl` and `NewTheorem Fin.ext_iff`. These are separate types, so no overwrite.
- No level has two `NewTactic` calls (which would cause silent overwrite). **Clean.**
- All `TacticDoc`/`TheoremDoc`/`DefinitionDoc` entries appear before or in the same file as their corresponding `NewTactic`/`NewTheorem`/`NewDefinition`. **Clean.**

### 3c. Statement exploitability

| Level | Statement | Exploits tested | Severity |
|-------|-----------|----------------|----------|
| L01 | `∃ i : Fin 5, i.val = 3` | `use ⟨0, by omega⟩` fails (0 ≠ 3). `exact default` fails (wrong type). Only `use ⟨3, by omega⟩` works. | **OK** |
| L02 | `i.val < 5` | Only `exact i.isLt`. | **OK** |
| L03 | `Fin.mk 2 h₁ = Fin.mk 2 h₂` | `rfl` works (proof irrelevance). | **P2** -- see notes below |
| L04 | `Fin.mk i.val i.isLt = i` | `rfl` works (eta). | **P2** -- same as L03 |
| L05 | `(h : Fin 0) → False` | Multiple valid paths, all engage with the concept. | **OK** |
| L06 | `(a b : Fin 1) → a = b` | `omega` bypasses `ext`. | **P2** -- acceptable |
| L07 | `(0 : Fin 3) ≠ (1 : Fin 3)` | `omega` and `decide` both work. | **OK** |
| L08 | `(Fin.last 4).val = 4` | `rfl` intended. | **OK** |
| L09 | `(Fin.castSucc i).val < 4` | `exact i.isLt` intended. `omega` also works. | **OK** -- both engage with the bound |
| L10 | `(Fin.succ i).val = i.val + 1` | `rfl` intended. | **OK** |
| L11 | `(Fin.last 3).val ≠ 4` | `intro h; omega` intended. `omega` alone does NOT work. `decide` does not work. | **OK** |
| L12 | `a.val = b.val` from `h : a = b` | `exact congr_arg Fin.val h` intended. Also `rw [h]` works. Also `simp [h]`. | **P2** -- see notes |
| L13 | `Fin.castSucc i ≠ Fin.last 4` | `Fin.castSucc_ne_last`, `Fin.castSucc_lt_last`, `ne_of_lt` all disabled. `omega`, `simp`, `decide` alone do not work. | **OK** |

**Notes on L03/L04 `rfl` bypass**: These levels teach `ext` but `rfl` closes the goal due to proof irrelevance (L03) and eta reduction (L04). This is inherent to the statement type -- making `rfl` not work here would require a genuinely different statement. The pedagogical cost is low: the learner who uses `rfl` still sees proof irrelevance in action, and the introduction text teaches `ext` regardless. The `ext` tactic gets genuine practice in L06 where `rfl` does NOT close the full goal.

**Notes on L12 `rw [h]` bypass**: The goal `a.val = b.val` from `h : a = b` can be closed by `rw [h]` (rewriting with `h`). This bypasses `congr_arg`. However, `rw [h]` is a legitimate proof technique that the learner already knows from NNG4, and it demonstrates the same concept (equal elements have equal components). The boss explicitly requires `congr_arg` in a context where `rw` does not work as cleanly (the goal is `False`, not an equality), so L12 remains useful even if the learner uses `rw` here.

### 3d. Interactive proof quality

| Level | Intended proof | Steps | Issue | Severity |
|-------|---------------|-------|-------|----------|
| L01 | `use ⟨3, by omega⟩` | 1 | One-liner with angle brackets + nested `by`. | **P2** -- conventional for first levels |
| L02 | `exact i.isLt` | 1 | Clean. | OK |
| L03 | `ext; rfl` | 2 | Clean. | OK |
| L04 | `ext; rfl` | 2 | Clean. | OK |
| L05 | `have h_lt := h.isLt; omega` | 2 | Clean. Intermediate feedback after `have`. | OK |
| L06 | `ext; omega` | 2 | Clean. | OK |
| L07 | `omega` | 1 | Clean. | OK |
| L08 | `rfl` | 1 | Definition observation. | OK |
| L09 | `exact i.isLt` | 1 | Clean. Requires recognizing the connection. | OK |
| L10 | `rfl` | 1 | Definition observation. | OK |
| L11 | `intro h; omega` | 2 | Clean. Intermediate feedback after `intro`. | OK |
| L12 | `exact congr_arg Fin.val h` | 1 | Term-mode one-liner. The learner must get the expression right in one go. | **P2** -- acceptable as a single-concept level |
| L13 | `intro h; have hv : i.val = 4 := congr_arg Fin.val h; omega` | 3 | The `have` step is a term-mode expression with type annotation. | **P2** -- mitigated by L12 seeding |

No P0 or P1 interactive quality issues remain. The L13 `have` step is the most complex single tactic call in the world, but L12 prepares the learner for the `congr_arg` part. The type annotation `: i.val = 4` is still a burden, but hints explain it and the introduction breaks it down.

---

## 4. Coverage sanity

### 4a. Core items coverage states

| Item | Axis | Importance | I | S | R | G | T | W | Notes |
|------|------|-----------|---|---|---|---|---|---|-------|
| M1: `Fin n` as subtype | MATH | core | L01 | L02-L06, L09, L12 | -- | L13 | L13 conc. | -- | Good closure. |
| M2: `Fin.val`, constructors, navigation | MATH | core | L01-L02 | L03-L04, L08-L10 | L09 | L13 | -- | -- | L09 now provides genuine retrieval of `.isLt`. |
| M3: Boundary cases (Fin 0, Fin 1) | MATH | core | L05, L06 | -- | -- | -- | L05, L06 conc. | L05 (C5) | Introduced but not revisited within W1. Acceptable -- W2/W3_ex will revisit. |
| N8: Coercion `↑` / `.val` | NOTATION | core | L02 | L08-L11 | -- | L13 | -- | -- | Explained in L02 prose. |
| C5: Fin 0 empty, not singleton | MISCONCEPTION | core | L05 | L06 | -- | -- | -- | L05 | Well-handled. |
| C6: Zero-indexing | MISCONCEPTION | core | L11 | -- | -- | -- | L11 conc. | L11 | **Improved**: L11 now forces confrontation via `intro h; omega`. |
| `ext` tactic | LEAN | core | L03 | L04, L06 | -- | NOT in boss | -- | -- | Same gap as R1 -- `ext` not tested in boss. |
| `omega` tactic | LEAN | supporting | L01 | L05, L06, L07 | L09 (indirect) | L13 | -- | -- | Well-covered. |
| `congr_arg` | LEAN/MOVE | supporting | **L12** | -- | -- | **L13** | L12 conc. | -- | **Fixed**: I in L12, G in L13. Proper closure. |
| `Fin.castSucc` | MATH | core (for boss) | L09 | -- | -- | L13 | -- | -- | L09 now requires reasoning (not just `rfl`). Better seeding. |
| `Fin.last` | MATH | core (for boss) | L08 | L11 | -- | L13 | -- | -- | L11 provides genuine practice. |
| `Fin.succ` | MATH | supporting | L10 | -- | -- | NOT in boss | -- | -- | Still introduced-only within W1. Deferred to W2. |
| `Fin.ext_iff` | LEAN | supporting | L03 | -- | -- | -- | -- | -- | Added to inventory in L03. |

### 4b. Coverage gaps

1. **`ext` not in boss**: The `ext` tactic is taught in L03-L06 but the boss (L13) does not use it. This is a residual gap from R1. However, the boss uses `congr_arg Fin.val`, which is the *converse* of `ext` -- L12's introduction explicitly frames it this way. The world teaches both directions of the value-level / Fin-level correspondence, even if the boss only tests one. **Severity: P3** (minor -- the learner has a coherent understanding of both tools).

2. **`Fin.succ` introduced but not used**: L10 introduces `Fin.succ` and it never appears again in W1. This was flagged in R1 and remains unchanged. The plan assigns `Fin.succ` to W2 for deeper use. **Severity: P3** (acceptable -- introduction-only items are fine when the next world provides closure).

3. **No concrete Fin construction after L01**: After L01, the learner never constructs a `Fin` element from scratch. All subsequent levels work with given `Fin` elements. This was flagged by the enrichment reviewer. The construction skill is exercised in W2 and W3_ex. **Severity: P3** (acceptable for a lecture world).

### 4c. Proof moves taught

| Move | Where taught | Where practiced | Where integrated | Status |
|------|-------------|----------------|-----------------|--------|
| Subtype extensionality (`ext`) | L03 | L04, L06 | (not in boss) | OK -- converse is in boss |
| Extract contradiction from impossible bound | L05 | L07, L11 | L13 | **Good** -- L11 provides additional practice (new since R1) |
| Intro + contradiction for `≠` | L07 | L11 | L13 | **Good** -- L11 now practices this move |
| Construct a Fin element | L01 | -- | -- | Deferred to W2/W3_ex |
| Use `.isLt` to get bound proof | L02 | L05 | L09, L13 | **Good** -- L09 provides additional practice (new since R1) |
| `congr_arg` for congruence | L12 | -- | L13 | **Good** -- properly seeded |

### 4d. Transfer

Transfer moments in the revised world:
- L01 conclusion: "In ordinary mathematics, we would say: Let i be a natural number with i < 5."
- L02 conclusion: connects `exact i.isLt` to "Since i is in {0,...,4}, we have i < 5"
- L05 conclusion: "If someone claims to have a natural number less than zero..."
- L06 conclusion: "The only natural number less than 1 is 0..."
- L07 conclusion: mental model "Fin n is the set {0, ..., n-1}"
- L09 conclusion: castSucc as "a fortiori" reasoning
- L11 conclusion: zero-indexing convention, connection to `Finset.range n`
- L12 conclusion: paper-proof correspondence for congr_arg
- L13 conclusion: detailed tactic-to-sentence mapping for the full proof

Transfer is solid and distributed throughout the world. L12's transfer paragraph ("this step corresponds to 'If a = b as elements of Fin n, then in particular their underlying values are equal'") is a good addition.

---

## 5. Granularity sanity

### 5a. Level-by-level granularity check

| Level | Dominant lesson | Too broad? | Too fine? | Notes |
|-------|----------------|-----------|----------|-------|
| L01 | Construct Fin 5 (existential) | No | No | Good first contact. Existential adds value. |
| L02 | Extract `.val` and `.isLt` | No | No | Clean. |
| L03 | Subtype extensionality | No | Borderline | `ext; rfl` is short but concept is important. OK. |
| L04 | Round-trip mk/val | No | Borderline | Same proof shape as L03 but distinct pedagogical point. |
| L05 | Fin 0 is empty | No | No | Excellent level. |
| L06 | Fin 1 is singleton | No | No | `ext; omega`. Good. |
| L07 | Distinct elements | No | No | Concretization. |
| L08 | Fin.last value | No | **Yes** | `rfl` observation. But serves as necessary definition introduction. |
| L09 | castSucc preserves bound | No | No | **Improved**: now requires `exact i.isLt`. Connects to L02. |
| L10 | Fin.succ increments | No | **Yes** | Still `rfl` observation. Serves as necessary definition introduction. |
| L11 | Zero-indexing misconception | No | No | **Improved**: now requires `intro h; omega`. Genuine reasoning. |
| L12 | congr_arg introduction | No | No | Clean single-concept level. Well-motivated. |
| L13 | Boss: castSucc ≠ last | No | No | Three-step integration proof. |

### 5b. Remaining `rfl` levels: L08 and L10

L08 and L10 are still `rfl` levels, but they serve a valid role: introducing definitions (`Fin.last` and `Fin.succ` respectively) via a definitional observation. Each is preceded or followed by a non-trivial level. The pattern is:

```
L08 (rfl: Fin.last) -> L09 (reasoning: castSucc bound) -> L10 (rfl: Fin.succ) -> L11 (reasoning: zero-indexing) -> L12 (reasoning: congr_arg)
```

This alternation is acceptable. The learner has a rhythm of "observe definition, then use it." No dead zone exists.

### 5c. World center of gravity

The world's center is "what is `Fin n` and how do you reason about it." Levels cover:
- **Definition** (L01-L04): construction, extraction, extensionality, round-trip
- **Boundary cases** (L05-L06): empty and singleton
- **Concretization** (L07): distinct elements
- **Navigation** (L08-L10): last, castSucc, succ -- with reasoning in L09
- **Misconception** (L11): zero-indexing -- with reasoning
- **New tool** (L12): congr_arg
- **Boss** (L13): integration

The center is stable and coherent. No splitting needed. 13 levels is a reasonable size for a lecture world covering this much material.

### 5d. Boss seeding

The boss (L13) requires:
1. `intro h` -- seeded in L07 (inequality), L11 (inequality)
2. `congr_arg Fin.val h` -- seeded in L12
3. Type annotation in `have` -- partially seeded (L05 uses `have h_lt := ...` without annotation, but the annotation pattern is explained in L13's introduction and hints)
4. `omega` for contradiction -- seeded in L05, L07, L11
5. Understanding that castSucc preserves value -- seeded in L09 (now with reasoning)
6. Understanding that last has value n -- seeded in L08

**Verdict: All boss subskills are seeded.** The weakest link is the type annotation on the `have` step, which is seen for the first time in the boss. However, this is a syntax burden, not a proof-move burden, and the hints walk through it. Acceptable.

---

## 6. Learner simulation

### 6a. Attentive novice

**Profile**: Completed NNG4. Comfortable with `rw`, `exact`, `apply`, `intro`, `cases`, `omega`. Reads introductions carefully.

**L01**: Reads introduction about finite index sets, understands the structure. Sees the existential goal `∃ i : Fin 5, i.val = 3`. Types `use ⟨3, by omega⟩`. **Improvement over R1**: the learner cannot accidentally bypass the lesson with `exact 0`.

**L02-L07**: Smooth progression. L05 is the standout -- genuine discovery. L07 provides a satisfying concrete payoff.

**L08**: Reads about `Fin.last`. Types `rfl`. Quick, but the introduction and conclusion provide good exposition. The learner forms the mental picture of "last element."

**L09**: Reads about `castSucc`. Sees the goal `(Fin.castSucc i).val < 4`. **Improvement over R1**: the hint says "the goal is really `i.val < 4`". The learner realizes that `i.isLt` provides exactly this. Types `exact i.isLt`. This is a genuine retrieval moment from L02 -- the learner connects two concepts (castSucc preserves value, plus the bound).

**L10**: Reads about `Fin.succ`. Types `rfl`. Quick, but the ASCII diagram in the conclusion is helpful.

**L11**: Reads about zero-indexing. Sees `(Fin.last 3).val ≠ 4`. **Improvement over R1**: must type `intro h; omega`. The hint explains that Lean reduces `(Fin.last 3).val` to `3`. The learner practices the `intro h` + contradiction pattern from L07 in a new context.

**L12**: New level. Reads about `congr_arg`. The concept is well-motivated: "you know `ext` goes one direction; this goes the other." Types `exact congr_arg Fin.val h`. The expression is moderately complex but the hint gives the exact syntax. The learner now has the pattern for L13.

**L13 (Boss)**: Reads the introduction. It explicitly lists the three steps and references L12. The learner:
1. Types `intro h` -- familiar from L07, L11
2. Types `have hv : i.val = 4 := congr_arg Fin.val h` -- the `congr_arg Fin.val h` part is familiar from L12. The type annotation is new syntax but explained in the introduction. Hint available if stuck.
3. Types `omega` -- familiar from L05, L07, L11

**First likely stuck point**: The type annotation `: i.val = 4` in step 2. The learner may type `have hv := congr_arg Fin.val h` (without annotation), which works but then `omega` may fail (because the hypothesis type is not reduced). If this happens, the hint suggests the annotated version.

**Most likely wrong move**: After `intro h`, trying `omega` (because it worked in L11). It fails. The hint then guides to `congr_arg`.

**Do hints rescue well?** Yes. Three hints, each at the correct proof state. The first says "try intro h", the second says "try have hv : i.val = 4 := congr_arg Fin.val h", the third says "try omega". Step-by-step.

**Is the level's lesson legible?** Yes. The introduction frames it as "castSucc and last partition Fin (n+1)." The conclusion translates to paper proof. The proof structure (assume equal, extract value consequence, find arithmetic contradiction) is clear.

**Overall novice experience**: Significantly improved from R1. The dead zone is eliminated. L12 properly scaffolds the boss. The world builds from simple observations to genuine reasoning to a satisfying integration proof.

### 6b. Experienced Lean user

**Profile**: Has used Lean 4 / mathlib. Knows `simp`, `exact?`, `omega`, `decide`.

**L01-L10**: Breezes through. May use `rfl` for L03/L04. Uses `omega` or `decide` where applicable.

**L11**: Types `intro h; omega` or `omega` -- oh wait, `omega` alone doesn't work here. Types `intro h; omega`. Mild engagement.

**L12**: Likely types `rw [h]` instead of `exact congr_arg Fin.val h`. This works and is a valid alternative. The lesson (both tools produce value-level equality from Fin-level equality) is still conveyed.

**L13**: **Key test.** The experienced user tries `exact Fin.castSucc_ne_last i` -- blocked by `DisabledTheorem`. Tries `exact ne_of_lt ...` -- blocked. Falls back to `intro h; simp [Fin.ext_iff] at h; omega` or the intended path. Either way, they must engage with the proof structure. **Improvement over R1**: the boss cannot be one-shotted.

**Avoidable friction**: `rw [h]` solving L12 means the experienced user might not actually learn `congr_arg` before the boss. If they then try `rw` in the boss (after `intro h`), `rw [h]` won't help directly because the goal is `False`, not an equality. They will be forced to find another approach, which may lead to `congr_arg` or to `simp at h`.

**Alias gaps**: `finZeroElim` is still mentioned in L05 prose but not in inventory. Minor -- documented as `Fin.elim0` which is the correct name.

**Inventory clutter**: L01 still dumps 10 tactics at once. Most are NNG4 baseline. The experienced user is unaffected, but the novice may see a cluttered inventory panel. This is a design choice that affects all worlds, not just W1.

---

## 7. Boss integrity check (L13)

### Seeded subskills

| Subskill | Seeded? | Where? |
|----------|---------|--------|
| `intro h` for ≠ goals | Yes | L07, L11 |
| `congr_arg Fin.val h` | **Yes** | L12 (new) |
| `omega` for contradiction | Yes | L05, L07, L11 |
| Understanding castSucc preserves value | Yes | L09 (improved -- now requires reasoning) |
| Understanding last has value n | Yes | L08, L11 (L11 uses Fin.last 3) |
| Type-annotated `have` | Partially | L05 uses `have := ...` without annotation; L13 intro explains the annotated form |

**Verdict: All subskills are seeded.** The type annotation is the weakest link but is a syntax burden, not a proof-move burden.

### Closure quality
The boss uses castSucc (L09), last (L08, L11), congr_arg (L12), intro for ≠ (L07, L11), and omega (L05, L07, L11). All are introduced AND practiced before the boss.

### Integration quality
The boss combines: intro, congr_arg, omega. It integrates understanding of castSucc's value-preserving property with last's value, and derives a contradiction via arithmetic. This exercises the core content of the world: what `Fin` elements are (value + proof), how navigation functions work, and how to reason at the value level.

The boss does NOT integrate: `ext` (L03-L06) or `Fin.succ` (L10). Both are reasonable exclusions -- `ext` is the converse direction (and L12 explicitly frames this), and `Fin.succ` is a supporting concept for future worlds.

### Surprise burden
None. All proof moves are familiar from prior levels. The only unfamiliar element is the type annotation on `have`, which is explained in the introduction and hints.

### Can the learner explain why the proof works?
Yes. The L13 conclusion provides an excellent translation:

> "Suppose castSucc(i) = last. Then their values are equal: i = n. But i < n since i in Fin n. Contradiction."

Each tactic step maps to a sentence. The learner can articulate the reasoning in plain English.

---

## 8. Course-role sanity

| Level | Intended role | Actual role | Miscast? |
|-------|--------------|-------------|----------|
| L01 | First contact (Fin, Fin.mk) | First contact (existential construction) | No |
| L02 | First contact (Fin.val, isLt) | First contact | No |
| L03 | First contact (ext) | First contact | No |
| L04 | Supported practice (round-trip) | Supported practice | No |
| L05 | First contact (Fin 0) + misconception | First contact + worked example | No |
| L06 | Supported practice (Fin 1, ext + omega) | Supported practice | No |
| L07 | Concretization / example | Example | No |
| L08 | Definition introduction (Fin.last) | Definition observation | **Marginal** -- still rfl, but acceptable as definition intro |
| L09 | First contact (castSucc) + retrieval (.isLt) | First contact + retrieval | **Improved** -- now exercises reasoning |
| L10 | Definition introduction (Fin.succ) | Definition observation | **Marginal** -- still rfl, same as L08 |
| L11 | Misconception confrontation (C6) | Misconception + reasoning | **Improved** -- now forces confrontation via contradiction |
| L12 | First contact (congr_arg) | First contact | No -- clean single-concept level |
| L13 | Boss | Boss (integration only) | **No** -- all material is seeded |

**Improvement over R1**: L09 and L11 now play their intended roles correctly. L12 is a properly cast first-contact level. L13 is a properly cast boss (no longer introduces new material).

---

## 9. Technical risks

1. **L12's `rw [h]` bypass**: The experienced user may solve L12 with `rw [h]` instead of `congr_arg Fin.val h`, then encounter the boss without having practiced `congr_arg`. The boss's hints will rescue, but the seeding is weakened. Consider adding `DisabledTactic rw` in L12 to force the `congr_arg` path. **Severity: P2.**

2. **`have hv := congr_arg Fin.val h` (without type annotation) in L13**: If the learner uses this form, `omega` may fail because the hypothesis type is `(Fin.castSucc i).val = (Fin.last 4).val` rather than `i.val = 4`. Lean's definitional reduction should handle this, but in practice `omega` does NOT see through `(Fin.last 4).val`. The learner would need `simp at hv` first. The hints guide to the annotated form, which avoids this issue, but a learner who deviates may get stuck. **Severity: P2.**

3. **L01 `NewTactic` dumps 10 tactics**: These are NNG4 baseline tactics that should be available from the start without explicit unlocking. Consider moving them to a Welcome level or `Metadata.lean` to avoid cluttering the first level. **Severity: P3** -- affects all worlds.

4. **`decide` not disabled in L07**: If W2 introduces `decide` as a new tactic, using it in W1 without introduction creates a forward dependency. Currently `decide` is not in L07's inventory but is available to the player. **Severity: P3** -- only matters if W2 explicitly teaches `decide` as new.

---

## 10. Ranked patch list

### P0 (Blocking)

**None.** All R1 P0 issues are resolved.

### P1 (High)

**None.** All R1 P1 issues are resolved.

### P2 (Medium -- should fix eventually)

**P2-1. Add `DisabledTactic rw` in L12 to force `congr_arg` practice.**
Without this, a learner who uses `rw [h]` in L12 enters the boss without having practiced `congr_arg`. The boss hints rescue, but the seeding is weaker than intended. Adding `DisabledTactic rw` in L12 ensures the learner must type `exact congr_arg Fin.val h`, which directly prepares them for the boss.

**P2-2. Add a hidden hint in L13 for the un-annotated `have` path.**
If the learner types `have hv := congr_arg Fin.val h` (without `: i.val = 4`), `omega` fails. Add a hidden hint at the proof state where `hv` has the un-reduced type, suggesting either `simp at hv` or the annotated form. This would catch the most common deviation from the intended path.

**P2-3. L03 and L04 are exploitable by `rfl` (bypassing `ext`).**
Same as R1 P2-1. This is inherent to the statement type (proof irrelevance / eta). `ext` gets genuine practice in L06 where `rfl` does not close the full goal. Low priority.

**P2-4. L06 bypass via `omega` (skipping `ext`).**
Same as R1 P2-6. `omega` can solve `(a b : Fin 1) → a = b` directly. Consider adding `DisabledTactic omega` in L06 to force the `ext; omega` path. This would give `ext` one more genuine practice opportunity.

### P3 (Low -- cosmetic / future-proofing)

**P3-1.** L01's `NewTactic` introduces 10 NNG4-baseline tactics. Consider moving to a Welcome level.

**P3-2.** L05 prose mentions `finZeroElim` but the inventory uses `Fin.elim0`. Consider removing the `finZeroElim` mention or adding a note that they are the same.

**P3-3.** `Fin.succ` (L10) is introduced but never reused in W1. Acceptable since W2 uses it.

---

## 11. What to playtest again after patching

If P2-1 and P2-2 are implemented:

1. **Re-audit L12** with `DisabledTactic rw`. Verify that no other common tactic bypasses `congr_arg`. Check that `exact congr_arg Fin.val h` is the only clean path.

2. **Re-audit L13** with the new hidden hint for un-annotated `have`. Verify the hint fires at the right proof state and provides actionable guidance.

3. **Simulate the novice through L12-L13** after patching. Confirm that the `congr_arg` pattern learned in L12 transfers cleanly to L13's more complex usage.

Otherwise, no further playtest is needed. The world is ship-ready.

---

## 12. Summary comparison: R1 vs R2

| Metric | R1 | R2 |
|--------|----|----|
| P0 issues | 2 | 0 |
| P1 issues | 4 | 0 |
| P2 issues | 6 | 4 |
| P3 issues | -- | 3 |
| Rubric average | 2.4 | 3.1 |
| Categories below 2 | 1 (Inventory at 1) | 0 |
| Red flags | 3 (missing docs, boss intro, no concrete example) | 0 |
| Boss exploitable? | Yes (one-shot) | No |
| Dead zone? | Yes (4 consecutive rfl) | No (alternating rfl/reasoning) |
| congr_arg seeded? | No | Yes (L12) |
| Statement pinned? (L01) | No (any value works) | Yes (existential pins value 3) |
| Verdict | CONDITIONAL PASS | **PASS** |
