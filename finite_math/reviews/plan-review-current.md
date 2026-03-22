# Plan Review: finite_math (Round 3)

**Reviewer**: plan-review prompt
**Date**: 2026-03-20
**Plan reviewed**: `finite_math/PLAN.md`
**Coverage map**: `finite_math/coverage-map.md`
**Course scope source**: `long_term.md` entry #1
**Prior reviews**: `plan-review-round1.md` (FAIL: 2 P0, 3 P1, 5 P2), `plan-review-round2.md` (FAIL: 1 P0, 0 P1, 4 P2)

---

## Round 2 Defect Resolution

| # | Severity | Defect | Status | Evidence |
|---|----------|--------|--------|----------|
| 1 | P0 | `world-list.txt` does not match PLAN.md (27 vs 29 worlds) | **FIXED** | `world-list.txt` now has 29 entries: separate Finsupp (line 25), Matrices (line 26), and PsetCounting (line 28). Matches PLAN.md exactly. |
| 2 | P2 | W12 L05 references descFactorial without introducing it | **FIXED** | W12 inventory (PLAN.md lines 501-503) now includes `NewDefinition Nat.descFactorial` and `NewTheorem Nat.descFactorial_zero Nat.descFactorial_succ`. |
| 3 | P2 | ℕ not Fintype counterexample missing | **FIXED** | W11 L07 (line 475) is explicitly: "ℕ is NOT finite — `ℕ` has no `Fintype` instance." World intro note (line 444) also mandates this warning. |
| 4 | P2 | List→Multiset→Finset supported practice compressed into W10 | **NOT FIXED** | W14 L08 (line 579) provides a cross-connection (Finset.sum is Multiset-based) but this is a single level within a big-op world, not dedicated retrieval. The coverage table (line 1095) acknowledges this by showing W14 L08 as a connection point, but introduction and primary supported practice remain in W10. |
| 5 | P2 | `ring`/`ring_nf` not introduced | **FIXED** | W15 inventory (line 612) includes `NewTactic calc ring ring_nf`. W15 L09 (line 624) explicitly teaches `ring` and `ring_nf`. |

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

No major topics missing. Lighter treatment of Finsupp, Matrix, and "finite sets as subtypes" is a defensible scoping choice for a basic course.

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
8. List → Multiset → Finset ladder — W10 (single world, cross-connection in W14 L08)
9. Proof by extensionality — W06, applied throughout: full treatment
10. Double counting / bijective proof — W27-W28-W29: adequate (improved over rounds 1-2)

### Coverage map items not in plan:

| Coverage map item | Status | Impact |
|-------------------|--------|--------|
| `List.map`, `List.filter`, `List.foldl`/`List.foldr` | Core LEAN; absent | Low — list-course material |
| `Finset.sum_image` / `Finset.prod_image` (reindexing) | Supporting; absent | Low — specialized |
| `Finset.sum_fiberwise` / `Finset.prod_fiberwise` | Supporting; absent | Low — specialized |

All previously missing items (Finset.Nonempty, simp only, calc, ring/ring_nf, ℕ not Fintype, descFactorial) are now addressed.

### Example plan alignment:

All 18 definitions in the coverage map's example plan have concrete examples. All 6 counterexamples are addressed.

---

## 3. World Graph Coherence

### Center of gravity:

Every world has a clear single center of gravity. The W25/W26 split (round 1 P1) is properly implemented — Finsupp and Matrices are separate worlds.

### Dependency ordering:

No dependency inversions. The factorial dependency error from round 1 is fixed: W17 introduces `Nat.factorial` (lines 685-686), W19 uses it (line 728).

The DAG in section 11 (lines 1356-1398) is consistent with world descriptions. Cross-phase dependencies are documented in the table at lines 1401-1413.

### World type mix:

| Type | Count | Worlds |
|------|-------|--------|
| Lecture | 15 | W02, W05-W07, W09-W11, W14-W16, W19-W21, W24, W27 |
| Onboarding/Lecture | 1 | W01 |
| Example | 2 | W22, W26 |
| Example + introduces content | 2 | W12, W17 |
| Lecture/Example | 1 | W25 |
| Pset | 6 | W04, W08, W13, W18, W23, W28 |
| Lecture (tuple-focused) | 1 | W03 |
| Review/Capstone | 1 | W29 |

Each pset is paired with its lecture worlds. Example worlds follow the theory they concretize. Phase 6 (W24-W26) has no dedicated pset, but W29 provides integration/retrieval for those lighter topics.

### world-list.txt alignment:

29 entries, matching PLAN.md exactly. Prior P0 resolved.

---

## 4. Proof-Move Coverage

The Transfer and Retrieval Plan (section 8) tracks 8 high-value moves with full 5-stage cycles and paper-proof transfer sentences:

1. Prove `x ∈ s` by construction — full cycle
2. Prove `s = t` by extensionality — full cycle
3. Cardinality arithmetic via card_* — full cycle
4. Finset induction — full cycle
5. Big-operator manipulation — full cycle
6. Bijective counting via Equiv — full cycle
7. Binomial coefficient identities — full cycle
8. Double counting — adequate cycle (W27→W28→W29)

### Moves from coverage map practiced but not in transfer plan:

- Case split on `Fin` elements — W01-W04, not tracked
- Prove non-membership / disjointness — used across many worlds, not tracked
- Nonempty → witness — now in W05 L08, coverage table tracks through W29, not in transfer plan
- Telescoping / cancellation in sums — not addressed
- Appeal to decidability — not addressed (likely intentional)

The proof-move map is solid. The 8 tracked moves cover the core skills. Untracked moves are either secondary or adequately practiced without explicit tracking.

---

## 5. Granularity Plan

### Novelty budgets:

Explicit rule (line 30): "at most one new burden per level." Level sketches are consistent with this.

W15 introduces 3 new tactics (calc, ring, ring_nf) but they are spread across separate levels (L08, L09), each introducing one. Consistent with the novelty budget.

### Boss skill seeding:

Boss Map (section 7, lines 1197-1229) maps each boss to prerequisite skills with level references. No boss depends on an untaught micro-skill.

### descFactorial:

W12 L05 now has `Nat.descFactorial` in its inventory (line 502). The level can be authored as specified.

### World lengths:

- W06: 10 levels (L01-L10). Long but each has a clear purpose.
- W09: 9 levels. Manageable.
- W10: 9 levels covering List→Multiset→Finset. Ambitious for one world but well-structured.

---

## 6. Coverage Closure

Using the Coverage Closure Table (section 5, lines 1082-1117):

### Strong closure (all 5 stages across 3+ worlds):

`Fin n`, `Fin` navigation, Tuples, `Finset` membership, `Finset.Nonempty` → witness, `Finset` operations, `simp only [...]`, `Finset.ext`, `Finset.image`, `Finset.card`, Inclusion-exclusion, `Fintype`, Fintype composition, `Equiv`-based counting, `calc`, `ring`/`ring_nf`, Big operators (basics + algebra), `sum_congr`, Finset induction, `Nat.factorial`, `Nat.choose`, `choose_symm`, `Finset.powerset`/`powersetCard`, `card_powerset`, `card_powersetCard`, Binomial theorem, `sum_range_choose`

### Partial closure:

| Item | Missing/thin stage | Assessment |
|------|-------------------|------------|
| Double counting | Supported practice is same world as introduction (W27) | W28 provides dedicated retrieval + transfer. 3 worlds total (W27, W28, W29). Acceptable — these are capstone techniques building on many earlier seeds (injection W07/W09, bijection W11/W12). |
| Pigeonhole | Same as double counting | Same assessment. |
| List→Multiset→Finset ladder | Introduction and supported practice both in W10 | W14 L08 provides a cross-connection (sum is Multiset-based). W13 provides retrieval. Partial but not blocking — the ladder is a conceptual backdrop, not a technique requiring deep practice. |
| `Finset.product` | Introduction and supported practice both in W24 | W29 provides retrieval. Only 2 worlds. Acceptable for a supporting topic. |
| `Finsupp` | No transfer stage | W25 intro, W29 retrieval. Acknowledged light treatment. |
| `Matrix` | No transfer stage | W26 intro, W29 retrieval. Acknowledged light treatment. |

### Closure rating summary:

- **Strong**: 27 of 33 tracked items
- **Partial**: 6 items (double counting, pigeonhole, abstraction ladder, product, Finsupp, Matrix)
- **Weak**: 0
- **Illusory**: 0

No weak or illusory items. Partial items are defensible design choices (light supporting topics) or acceptable compressions (capstone techniques with earlier seeds).

---

## 7. Transfer Plan

Present and detailed for 8 high-value moves (section 8, lines 1231-1287). Each specifies: introduction, supported practice, unsupported retrieval, transfer to fresh surface, and paper-proof transfer sentence.

### Remaining gaps:

- List→Multiset→Finset ladder: no entry in transfer plan
- Fin case analysis: no entry
- Nonempty → witness: coverage-table tracked but no transfer-plan entry

These are secondary moves. Not blocking.

---

## 8. Inventory Release Plan

Thorough (section 6, lines 1119-1195). Per-phase tables with tactics, theorems/definitions, disabled items, and rationale.

Key inventory milestones:
- W01: `omega` for Fin arithmetic
- W03: `funext` for function extensionality
- W05: `decide` re-enabled for small finset goals
- W06: `ext`, `simp_only` introduced; lattice aliases disabled
- W09: `norm_num` re-enabled for cardinality computations
- W12: `Nat.descFactorial` introduced (fixed from round 2)
- W14: Big operators introduced
- W15: `calc`, `ring`, `ring_nf` introduced (fixed from round 2)
- W17: `Nat.factorial` introduced (fixed from round 1)

Baseline disabled: `trivial`, `decide` (until W05), `native_decide`, `simp`, `aesop`, `simp_all`. Lattice aliases always disabled. Per-level gating notes are specific.

No gaps identified.

---

## 9. Example and Counterexample Plan

### Examples:

All 18 definitions in the coverage map's example plan have concrete examples. Three dedicated Example worlds (W12, W17, W22) plus W25 and W26 as lecture/example hybrids.

### Counterexamples:

| Counterexample | Planned | Where |
|----------------|---------|-------|
| `Finset.image` shrinks card | Yes | W07 L04 |
| ℕ not Fintype | Yes | W11 L07 + world intro |
| `List.Nodup` failure | Yes | W10 L06 |
| `Multiset ≠ Finset` | Yes | W10 L05, L08 |
| `Nat.choose n k = 0` when k > n | Yes | W19 L06 |
| `Finset.insert` idempotence | Yes | W05 L07 |

All 6 counterexamples from the coverage map are addressed. The ℕ not Fintype gap from rounds 1-2 is fixed.

---

## Defects Summary

### P0 (blocking):

None.

### P1 (high):

None.

### P2 (medium):

1. **List→Multiset→Finset supported practice still compressed into W10**: Introduction and supported practice are the same world. W14 L08 provides a cross-connection but not dedicated practice. Consider adding a level in W13 that requires choosing the correct abstraction layer (e.g., proving a fact about `List.toFinset` that requires reasoning about `Nodup`).

2. **Phase 6 has no pset**: W24 (Products), W25 (Finsupp), W26 (Matrices) have no dedicated problem set. W29 provides retrieval but without a pset in between, the learner jumps from introduction to capstone integration. Acceptable for light/advanced topics, but a 3-4 level pset could strengthen the Phase 6 → Phase 7 transition.

3. **Finsupp and Matrix have no transfer stage**: Both are introduced in their own world and only retrieved in W29. No fresh surface forms. This is the acknowledged cost of keeping them light. If either proves more important during authoring, a transfer level in W29 could be designed to use these in a genuinely new context (not just "do another Matrix problem").

---

## Specific Recommendations (ranked)

1. **(P2)** Consider adding one level in W13 (PsetCardinality) that requires the learner to choose whether to reason at the List, Multiset, or Finset level — this would give the abstraction ladder a retrieval point outside W10.

2. **(P2)** During authoring of W29 (Finale), ensure at least one level uses Finsupp or Matrix in a context genuinely different from W25/W26 (e.g., a Finsupp-based counting argument, or a matrix cardinality result). This converts the final retrieval into a transfer.

3. **(P2)** If Phase 6 worlds prove substantial enough during authoring, consider inserting a 3-4 level PsetAdvanced between W26 and W27. This decision can be deferred to authoring.

---

## Overall Verdict: PASS

All round 1 and round 2 blocking defects are resolved:
- Factorial dependency inversion: fixed (W17 introduces factorial)
- Inclusion-exclusion supported practice: fixed (W12 L06)
- Double counting/pigeonhole closure: fixed (W28 PsetCounting added)
- Nonempty → witness: fixed (W05 L08)
- W25 two centers of gravity: fixed (separate W25/W26)
- world-list.txt mismatch: fixed (29 entries matching PLAN.md)
- descFactorial introduction: fixed (W12 inventory)
- ℕ not Fintype: fixed (W11 L07)
- ring/ring_nf: fixed (W15)

Remaining issues are all P2 — minor gaps in coverage closure for supporting topics and the abstraction ladder. None meet FAIL criteria:
- No major topics missing from long_term.md
- Proof-move map tracks 8 moves with full 5-stage cycles
- No core items with weak or illusory closure (6 partial, all defensible)
- All major definitions have example plans
- No dependency errors in world graph
- Transfer plan present and detailed

The plan is ready for authoring.
