# Plan Review: finite_math (Round 2)

**Reviewer**: plan-review prompt
**Date**: 2026-03-20
**Plan reviewed**: `finite_math/PLAN.md`
**Coverage map**: `finite_math/coverage-map.md`
**Course scope source**: `long_term.md` entry #1
**Prior review**: `plan-review-round1.md` (FAIL with 2 P0, 3 P1, 5 P2)

---

## Round 1 Defect Resolution

Checking whether each round 1 defect was addressed:

| # | Severity | Defect | Status | Evidence |
|---|----------|--------|--------|----------|
| 1 | P0 | Factorial dependency inversion (W17 uses factorial before W19 introduces it) | **FIXED** | W17 now has `NewDefinition Nat.factorial` and `NewTheorem Nat.factorial_zero Nat.factorial_succ` in its inventory. W19 says "(`Nat.factorial` was introduced in W17.)". Coverage table shows factorial introduced in W17. |
| 2 | P0 | Inclusion-exclusion has no supported practice stage | **FIXED** | W12 L06 now explicitly includes scaffolded inclusion-exclusion practice. Coverage table updated: W09 (intro) → W12 (supported) → W13 (retrieval). |
| 3 | P1 | Double counting / pigeonhole weak closure | **FIXED** | W28 (PsetCounting) added with 6 levels of dedicated practice. Double counting closure: W27→W27→W28→W29→W29. |
| 4 | P1 | Finset.Nonempty → witness absent | **FIXED** | W05 L08 teaches the move. Inventory includes `Finset.Nonempty` and `Finset.Nonempty.some_mem`. Coverage table tracks it through W05→W09→W13→W27→W29. |
| 5 | P1 | W25 has two centers of gravity (Finsupp + Matrix) | **FIXED in PLAN.md** | W25 (Finsupp) and W26 (Matrices) are now separate worlds. **BUT**: `world-list.txt` still shows combined "FinsuppAndMatrices" as a single entry — see P0 defect below. |
| 6 | P2 | `simp` with Finset lemmas never taught | **FIXED** | W06 L09 teaches `simp only [...]` with Finset lemmas. Coverage table tracks it. |
| 7 | P2 | `calc` blocks not introduced | **FIXED** | W15 L08 introduces `calc` blocks. Coverage table tracks it. |
| 8 | P2 | World dependency DAG undocumented | **FIXED** | Section 11 has an explicit ASCII DAG with cross-phase edges. |
| 9 | P2 | ℕ not Fintype counterexample missing | **NOT FIXED** | No explicit mention in W11 or elsewhere. |
| 10 | P2 | List→Multiset→Finset compressed into W10 | **NOT FIXED** | Introduction and supported practice are still both in W10. |

---

## 1. Scope Completeness

All major topics from `long_term.md` entry #1 are represented:

| Topic | Where | Depth |
|-------|-------|-------|
| `Fin` | W01-W04 | thorough |
| `Fintype` | W11-W13 | thorough |
| `Finset` | W05-W09 | thorough |
| Finite sets as subtypes | W01 (Fin as subtype) | light — `{x // x ∈ s}` / `Set.Finite` absent |
| Lists vs multisets | W10 | adequate |
| Permutations of lists | W10 (List.Perm) | adequate |
| Finitely supported functions | W25 | light |
| Finite products of finsets | W24 | adequate |
| Matrices over finite index types | W26 | light |
| Big operators | W14-W18 | thorough |
| Binomial coefficients | W19-W22 | thorough |
| Factorials | W17, W19 | adequate |
| Counting identities | W19-W23, W27 | thorough |

No major topics missing. Lighter treatment of Finsupp, Matrix, and "finite sets as subtypes" is defensible for a basic course.

---

## 2. Coverage Map Alignment

### Core items (section 2 of coverage map) — all 10 addressed:

1. `Fin n` — W01-W04: full treatment
2. `Finset` — W05-W08: full treatment
3. `Fintype` — W11-W13: full treatment
4. `Finset.card` and cardinality — W09, W12, W20, W24: full treatment
5. Big operators — W14-W18: full treatment
6. Binomial coefficients — W19-W23: full treatment
7. Induction over finsets — W16-W18: full treatment
8. List → Multiset → Finset ladder — W10: single world (compressed — see closure)
9. Proof by extensionality — W06, applied throughout: full treatment
10. Double counting / bijective proof — W27-W28: improved from round 1

### Coverage map items not in plan:

| Coverage map item | Status | Impact |
|-------------------|--------|--------|
| `List.map`, `List.filter`, `List.foldl`/`List.foldr` | Listed core LEAN; absent | Low — list-course material |
| `Finset.sum_image` / `Finset.prod_image` (reindexing) | Listed supporting; absent | Low — specialized |
| `Finset.sum_fiberwise` / `Finset.prod_fiberwise` | Listed supporting; absent | Low — specialized |
| `ring`/`ring_nf` | Listed supporting LEAN; absent | Low-medium — useful in Phase 4/5 arithmetic |
| ℕ not Fintype counterexample | Listed in examples; absent | Low |

### Example plan alignment:

All 18 definitions in the coverage map's example plan have corresponding concrete examples. All 6 counterexamples are addressed except ℕ not Fintype.

---

## 3. World Graph Coherence

### Center of gravity:

Every world has a clear single center of gravity. The round 1 issue (Finsupp + Matrix combined) is fixed in PLAN.md — they are now separate worlds W25 and W26.

### Dependency ordering:

The factorial dependency inversion (round 1 P0 #1) is fixed. W17 introduces factorial; W19 uses it.

No other dependency inversions found. The DAG in section 11 is consistent with the world descriptions.

### World type mix:

| Type | Count | Worlds |
|------|-------|--------|
| Lecture | 15 | W02, W05-W07, W09-W11, W14-W16, W19-W21, W24, W27 |
| Onboarding/Lecture | 1 | W01 |
| Example | 3 | W12, W22, W26 |
| Example + introduces new content | 1 | W17 |
| Lecture/Example | 1 | W25 |
| Pset | 6 | W04, W08, W13, W18, W23, W28 |
| Lecture (tuple-focused) | 1 | W03 |
| Review/Capstone | 1 | W29 |

Each pset is properly paired with its lecture worlds. Example worlds follow the theory they concretize. Mix is deliberate.

### Discrepancy with world-list.txt:

PLAN.md describes 29 worlds. `world-list.txt` has 27 worlds: it still lists "FinsuppAndMatrices" as one combined world and omits "PsetCounting". This is a concrete inconsistency that will cause automation to use the wrong world list.

---

## 4. Proof-Move Coverage

The plan tracks 8 high-value moves in the Transfer and Retrieval Plan (section 8), each with introduction → supported practice → unsupported retrieval → integration → transfer stages. Paper-proof transfer sentences are provided.

### Tracked moves with full cycles:

1. Prove `x ∈ s` by construction
2. Prove `s = t` by extensionality
3. Cardinality arithmetic via card_*
4. Finset induction
5. Big-operator manipulation
6. Bijective counting via Equiv
7. Binomial coefficient identities
8. Double counting (improved from round 1; still compressed within W27-W29)

### Moves from coverage map not tracked:

- Case split on `Fin` elements — practiced W01-W04 but not in transfer plan
- Prove non-membership / disjointness — used across many worlds but not tracked
- Telescoping / cancellation in sums — not addressed
- Appeal to decidability — not addressed (likely intentional)

The proof-move map is not absent or superficial. It does not cover every move from the coverage map, but covers the 8 highest-value ones with clear 5-stage cycles.

---

## 5. Granularity Plan

### Novelty budgets:

Explicit: "at most one new burden per level." Level sketches are consistent with this rule across all 29 worlds.

### Boss skill seeding:

The Boss Map (section 7) maps each boss to prerequisite skills with level references. No boss depends on an untaught micro-skill.

### W12 L05 references `descFactorial`:

W12 L05 says "Connection to descFactorial" but `Nat.descFactorial` is in the coverage map's "delay" list and is never introduced in any world's inventory. This level cannot reference `descFactorial` as a teaching point without introducing it. This is not a dependency inversion (it says "connection to" not "use"), but the authoring agent will need to handle this carefully — either introduce `descFactorial` in W12's inventory or drop the reference.

### Potential length concerns:

- W06: 10 levels (L01-L09 + boss at L10). Long but each level has a clear purpose.
- W09: 9 levels. Manageable.
- W10: 9 levels covering the full List→Multiset→Finset story. Ambitious for one world.

---

## 6. Coverage Closure

Using the plan's Coverage Closure Table (section 5):

### Strong closure (all 5 stages clearly present, across 3+ worlds):

`Fin n`, `Fin` navigation, Tuples, `Finset` membership, `Finset.Nonempty` → witness, `Finset` operations, `simp only [...]`, `Finset.ext`, `Finset.image`, `Finset.card`, Inclusion-exclusion (now fixed), `Fintype`, Fintype composition, `Equiv`-based counting, `calc`, Big operators (basics + algebra), `sum_congr`, Finset induction, `Nat.factorial`, `Nat.choose`, `choose_symm`, `Finset.powerset`/`powersetCard`, `card_powerset`, `card_powersetCard`, Binomial theorem, `sum_range_choose`

### Partial closure (some stages present but thin):

| Item | Missing/thin stage | Assessment |
|------|-------------------|------------|
| Double counting | Supported practice is same world as introduction (W27) | Improved from round 1 — W28 provides dedicated retrieval + transfer. Still only 3 worlds total (W27, W28, W29). Acceptable given these are capstone techniques. |
| Pigeonhole | Same as double counting | Same assessment. |
| List→Multiset→Finset ladder | Introduction and supported practice both in W10 | No supported-practice level in a different world. W13 retrieval is unsupported. The concept is mentioned in W14 context (sum is Multiset-based) but not explicitly practiced. |
| `Finset.product` | Introduction and supported practice both in W24 | All later stages compressed into W29. Only 2 worlds total. |
| `Finsupp` | No transfer stage | Introduced W25, retrieved W29. No fresh surface form. |
| `Matrix` | No transfer stage | Introduced W26, retrieved W29. No fresh surface form. |

### Closure rating summary:

- **Strong**: 26 out of 32 tracked items
- **Partial**: 6 items (double counting, pigeonhole, abstraction ladder, product, Finsupp, Matrix)
- **Weak**: 0
- **Illusory**: 0

The partial items for Finsupp/Matrix are acknowledged design choices (light treatment). Double counting/pigeonhole are improved from round 1. The abstraction ladder compression is a minor remaining gap.

---

## 7. Transfer Plan

Present and detailed for 8 high-value moves (section 8). Each specifies: where introduced, where practiced with support, where retrieved without prompting, where transferred to fresh surface, and paper-proof transfer sentence.

### Remaining gaps:

- List→Multiset→Finset ladder has no entry in the transfer plan
- Fin case analysis has no entry
- Non-membership proofs have no entry

These are secondary moves — the 8 tracked moves cover the core skills. Not a blocking issue.

---

## 8. Inventory Release Plan

Thorough (section 6). Per-phase tables with tactics, theorems/definitions, disabled items, and rationale.

- `omega` in W01 when needed
- `funext` in W03, `ext` in W06, `decide` re-enabled W05, `norm_num` re-enabled W09
- `simp only` in W06 (fixed from round 1)
- `calc` in W15 (fixed from round 1)
- Lattice aliases always disabled
- Per-level gating notes specific and well-reasoned
- Baseline disabled list matches CLAUDE.md

### Minor gap:

- `ring`/`ring_nf` from coverage map (supporting LEAN) not introduced. Would be useful in W15-W17 (big-operator algebra) and W19 (binomial arithmetic). Not blocking.

---

## 9. Example and Counterexample Plan

### Examples:

All 18 definitions in the coverage map's example plan have concrete examples. Three dedicated Example worlds (W12, W17, W22) plus W25 and W26 as lecture/example hybrids. Strong.

### Counterexamples:

| Counterexample | Planned | Where |
|----------------|---------|-------|
| `Finset.image` shrinks card | Yes | W07 L04 |
| ℕ not Fintype | **No** | — |
| `List.Nodup` failure | Yes | W10 L06 |
| `Multiset ≠ Finset` | Yes | W10 L05, L08 |
| `Nat.choose n k = 0` when k > n | Yes | W19 L06 |
| `Finset.insert` idempotence | Yes | W05 L07 |

One counterexample still missing: ℕ has no `Fintype` instance. Could be a one-line warning in W11 intro text. Not blocking.

---

## Defects Summary

### P0 (blocking — must fix before authoring):

1. **`world-list.txt` does not match PLAN.md**: PLAN.md has 29 worlds with W25=Finsupp, W26=Matrices, W28=PsetCounting. `world-list.txt` has 27 worlds with combined "FinsuppAndMatrices" and no "PsetCounting". The automation uses `world-list.txt`, so authoring will use the wrong world structure. **Fix**: Update `world-list.txt` to match the 29 worlds in PLAN.md.

### P1 (high — significant gaps):

None remaining. All round 1 P1 defects are resolved.

### P2 (medium — improvements):

2. **W12 L05 references `descFactorial` without introducing it**: The level says "Connection to descFactorial" but `Nat.descFactorial` is never in any world's inventory. **Fix**: Either add `Nat.descFactorial` to W12's inventory or reword L05 to avoid referencing an untaught concept.

3. **ℕ not Fintype counterexample still missing**: Listed in coverage map examples. **Fix**: Add a warning or brief note in W11 intro.

4. **List→Multiset→Finset supported practice compressed**: Introduction and supported practice are both W10. **Fix**: Add a level in W13 or W14 that requires choosing the correct abstraction layer or connects `Finset.sum` to `Multiset.sum`.

5. **`ring`/`ring_nf` not introduced**: Listed as supporting LEAN in coverage map. Useful for arithmetic in Phases 4-5. **Fix**: Consider introducing in W15 alongside `calc`.

---

## Specific Recommendations (ranked)

1. **(P0)** Update `world-list.txt` to match PLAN.md: replace "FinsuppAndMatrices" with "Finsupp" and "Matrices" as separate entries, and add "PsetCounting" between "CountingTechniques" and "Finale".

2. **(P2)** Either add `Nat.descFactorial` to W12's inventory with a brief teaching level, or reword W12 L05 to avoid the reference.

3. **(P2)** Add a brief "ℕ has no `Fintype` instance" warning in W11 intro text.

4. **(P2)** Consider adding a level in W14 that connects `Finset.sum` to the Multiset layer, giving the abstraction ladder a retrieval point outside W10.

5. **(P2)** Consider introducing `ring`/`ring_nf` in W15 as a supporting tactic for algebraic simplification in big-operator proofs.

---

## Overall Verdict: FAIL

The plan is strong. All round 1 P0 and P1 defects have been addressed in PLAN.md. The coverage closure, proof-move tracking, inventory release, boss seeding, and example plans are all well above average.

However, one issue triggers FAIL:

1. **`world-list.txt` does not match PLAN.md** — the automation file lists 27 worlds while the plan describes 29. This means authoring will use the wrong world structure (combined FinsuppAndMatrices instead of separate worlds, and no PsetCounting). This is a concrete operational blocker.

This is trivially fixable — update the world-list file. After that single fix, remaining issues are all P2 and the plan should pass.
