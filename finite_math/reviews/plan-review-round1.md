# Plan Review: finite_math

**Reviewer**: plan-review prompt
**Date**: 2026-03-20
**Plan reviewed**: `finite_math/PLAN.md`
**Coverage map**: `finite_math/coverage-map.md`
**Course scope source**: `long_term.md` entry #1

---

## 1. Scope Completeness

The plan covers every major topic from `long_term.md`:

| Topic from long_term.md | Where in plan | Depth |
|--------------------------|---------------|-------|
| `Fin` | W01-W04 | thorough |
| `Fintype` | W11-W13 | thorough |
| `Finset` | W05-W09 | thorough |
| Finite sets as subtypes | W01 (Fin as subtype) | light — the broader `{x // x ∈ s}` / `Set.Finite` story is absent |
| Lists vs multisets | W10 | adequate |
| Permutations of lists | W10 (List.Perm) | adequate |
| Finitely supported functions | W25 | light |
| Finite products of finsets | W24 | adequate |
| Matrices over finite index types | W25 | light |
| Big operators | W14-W18 | thorough |
| Binomial coefficients | W19-W22 | thorough |
| Factorials | W19 | adequate |
| Counting identities | W19-W23, W26 | thorough |

**Finding**: No major topics are missing. The lighter treatment of Finsupp, Matrix, and "finite sets as subtypes" is a defensible scoping choice for a basic course. The plan explicitly identifies the light treatment of Finsupp/Matrix as a known risk (Risk 8).

---

## 2. Coverage Map Alignment

### Core items (section 2 of coverage map) — all 10 addressed:

1. `Fin n` — W01-W04: full treatment ✓
2. `Finset` — W05-W08: full treatment ✓
3. `Fintype` — W11-W13: full treatment ✓
4. `Finset.card` and cardinality — W09, W20, W24, W26: full treatment ✓
5. Big operators — W14-W18: full treatment ✓
6. Binomial coefficients — W19-W23: full treatment ✓
7. Induction over finsets — W16-W18: full treatment ✓
8. List → Multiset → Finset ladder — W10: single world, no supported practice outside W10 (see closure analysis)
9. Proof by extensionality — W06, used across many later worlds ✓
10. Double counting / bijective proof — W26-W27: compressed (see closure analysis)

### Coverage map items not addressed in plan:

| Coverage map item | Status | Impact |
|-------------------|--------|--------|
| `List.map`, `List.filter`, `List.foldl`/`List.foldr` | Listed as core LEAN; absent from plan | Low — these are list-course material, not essential for the finite math scope |
| "Choose an element from a nonempty finset" (`Finset.Nonempty` → witness) | Listed as core MOVE; absent from plan | Medium — a practical proof move used in later courses |
| `Finset.sum_image` / `Finset.prod_image` (reindexing) | Listed as supporting; absent | Low — specialized |
| `Finset.sum_fiberwise` / `Finset.prod_fiberwise` | Listed as supporting; absent | Low — specialized |
| `calc` blocks | Listed as core LEAN; not introduced | Medium — a generally useful Lean skill not explicitly taught |
| `ℕ` is not a `Fintype` (counterexample) | Listed in examples; absent | Low — could be mentioned in W11 intro text |

### Example plan alignment:

All 18 definitions in the coverage map's example plan have corresponding concrete examples in the world graph. All 6 counterexamples are addressed. This is strong.

---

## 3. World Graph Coherence

### Center of gravity:

Every world except W25 has a clear single center of gravity. W25 combines Finsupp and Matrix — two unrelated topics — in one world. The plan acknowledges this as Risk 8 and proposes splitting or merging as needed during authoring.

### Dependency ordering:

**DEPENDENCY ERROR**: W17 (SummationFormulas) L03 states: `∏ i in range n, (i + 1) = Nat.factorial n`. But `Nat.factorial` is not introduced until W19 (BinomialCoefficients). W17's inventory section says "None new. Retrieval of W14-W16 inventory" — confirming factorial is not part of W17's inventory. Yet L03 uses it. The dependency graph allows a learner to reach W17 without passing through W19 (W17 depends on W16; W19 depends on W16 and W09; no dependency W17→W19).

The coverage closure table compounds this: it lists `Nat.factorial` as "integrated" in W17 and "introduced" in W19 — integration before introduction.

### Branching:

The world graph allows Phases 3 and 4 to be partially parallel (W14 depends on W06, not on any Phase 3 world). This is fine but not explicitly documented. The numbered phases suggest a linear order that the dependency graph doesn't enforce. Worth noting in the plan for implementers.

### World type mix:

| Type | Count | Worlds |
|------|-------|--------|
| Lecture | 16 | W01-W03, W05-W07, W09-W11, W14-W16, W19-W21, W24, W26 |
| Onboarding hybrid | 1 | W01 |
| Example | 3 | W12, W17, W22 |
| Pset | 5 | W04, W08, W13, W18, W23 |
| Lecture+Example | 1 | W25 |
| Review/Capstone | 1 | W27 |

Each pset is properly paired with its lecture worlds. Example worlds follow the abstract theory they concretize. The mix is deliberate and well-distributed.

---

## 4. Proof-Move Coverage

The plan tracks 8 high-value moves in the Transfer and Retrieval Plan (section 8), each with 5 stages:

1. Prove `x ∈ s` by construction — full cycle ✓
2. Prove `s = t` by extensionality — full cycle ✓
3. Cardinality arithmetic via card_* — full cycle ✓
4. Finset induction — full cycle ✓
5. Big-operator manipulation — full cycle ✓
6. Bijective counting via Equiv — full cycle ✓
7. Binomial coefficient identities — full cycle ✓
8. Double counting — thin cycle (see section 6)

### Moves from coverage map not tracked:

- Case split on `Fin` elements — practiced in W01-W04 but not in the transfer plan
- Prove non-membership / disjointness — used across many worlds but not tracked
- Choose element from nonempty finset — core move, not addressed
- Telescoping / cancellation in sums — not addressed
- Appeal to decidability — not addressed (may be intentional given `decide` gating)

The proof-move map is present in distributed form (per-world proof-move goals + transfer plan + boss map). It is not absent or superficial, but it does not cover all core moves from the coverage map.

---

## 5. Granularity Plan

### Novelty budgets:

Each level isolates one dominant lesson. The plan states the rule explicitly: "at most one new burden per level." Level sketches are consistent with this rule.

### Boss skill seeding:

The Boss Map (section 7) explicitly maps each boss to its prerequisite skills with level references. Every boss integrates previously-taught skills. No boss depends on an untaught micro-skill (with the exception of the factorial issue in W17).

### Potential concerns:

- W06 has 9 levels — slightly long, but each level has a clear purpose
- W09 has 9 levels covering many card_* lemmas — individually focused, acceptable
- W10 has 9 levels covering the full List→Multiset→Finset story in one world — ambitious for a single world

---

## 6. Coverage Closure

Using the plan's own Coverage Closure Table (section 5), evaluated against the five-stage model:

### Strong closure (all 5 stages clearly present):

`Fin n`, `Fin` navigation, Tuples, `Finset` membership, `Finset` operations, `Finset.ext`, `Finset.image`, `Finset.card`, `Fintype`, Fintype composition, Equiv-based counting, Big operators (basics and algebra), `sum_congr`, Finset induction, `Nat.choose`, `choose_symm`, `Finset.powerset`/`powersetCard`, `card_powerset`, `card_powersetCard`, Binomial theorem, `sum_range_choose`

### Partial closure:

| Item | Missing stage | Issue |
|------|--------------|-------|
| Inclusion-exclusion | Supported practice | Goes from introduction (W09 L06) directly to pset (W13). W13 IS unsupported retrieval, yet the closure table lists it as both supported practice AND unsupported retrieval — contradictory. No intermediate scaffolded world uses inclusion-exclusion. |
| List→Multiset→Finset ladder | Distinct supported practice | Introduction and supported practice are both W10. The ladder concept is never used with scaffolding in a different world before retrieval in W13. |
| `Finset.product` | Supported practice, integration, transfer | Introduction and supported practice both in W24. All later stages compressed into W27. |
| `Finsupp` | Transfer | No transfer stage. Introduced and practiced in W25, retrieved in W27, but never appears in a fresh surface form. |
| `Matrix` | Transfer | Same as Finsupp. |

### Weak closure:

| Item | Issue |
|------|-------|
| Double counting | Introduced in W26, practiced in W26, retrieved/integrated/transferred all in W27. Two worlds total. The plan acknowledges this as Risk 7 and proposes a mitigation (add PsetCounting if needed), but the current plan does not include that world. |
| Pigeonhole | Same structure as double counting — compressed into W26-W27. |

### Dependency inversion:

| Item | Issue |
|------|-------|
| `Nat.factorial` | Listed as integrated in W17, introduced in W19. W17 precedes W19 in the dependency graph. |

---

## 7. Transfer Plan

The Transfer and Retrieval Plan (section 8) is present and detailed for 8 high-value moves. Each move lists: where introduced, where practiced with support, where retrieved without prompting, where transferred to a fresh surface form. Paper-proof transfer sentences are provided for each move.

### Gaps:

- Double counting and pigeonhole transfer is thin (acknowledged)
- No transfer tracking for: Fin case analysis, non-membership proofs, nonempty-finset witness extraction, decidability appeals
- The List→Multiset→Finset ladder has no transfer entry in section 8

---

## 8. Inventory Release Plan

The inventory release plan (section 6) is thorough:

- Tactics are gated and released deliberately ✓
- `omega` introduced in W01 when first needed ✓
- `funext` in W03, `ext` in W06, `decide` re-enabled in W05, `norm_num` re-enabled in W09 ✓
- Lattice aliases always disabled ✓
- Per-level gating notes are specific and well-reasoned ✓
- Baseline disabled list matches CLAUDE.md operational lessons ✓
- The plan identifies `fin_cases`, `by_cases`, `norm_num`, `decide`, and `ext` as per-level gates ✓

### Gaps:

- `simp` is baseline disabled and never re-enabled. The coverage map lists "`simp` with Finset lemmas" as a core LEAN skill. Learners finish the course unable to use `simp [Finset.mem_insert, ...]` — a pervasive pattern in real mathlib proofs. If this is intentional, it should be stated as a deliberate pedagogical choice.
- `calc` blocks are listed as core in the coverage map but never introduced. Multi-step `calc` reasoning is a transferable skill.
- `ring`/`ring_nf` listed as supporting in coverage map, not introduced. These would be useful in Phase 4 (big-operator algebra) and Phase 5 (binomial arithmetic).

---

## 9. Example and Counterexample Plan

### Examples:

All 18 definitions in the coverage map's example plan have concrete examples planned in specific worlds and levels. The three dedicated Example worlds (W12, W17, W22) provide substantial concretization after abstract theory. This is strong.

### Counterexamples:

| Counterexample | Planned | Where |
|----------------|---------|-------|
| `Finset.image` shrinks card (non-injective) | ✓ | W07 L04 |
| `ℕ` not Fintype | missing | — |
| `List.Nodup` failure | ✓ | W10 L06 |
| `Multiset ≠ Finset` (duplicates) | ✓ | W10 L05, L08 |
| `Nat.choose n k = 0` when k > n | ✓ | W19 L07 |
| `Finset.insert` idempotence | ✓ | W05 L07 |

One counterexample missing: "ℕ has no Fintype instance." This could be a brief note in W11's introduction.

---

## Defects Summary

### P0 (blocking — must fix before authoring):

1. **Factorial dependency inversion**: W17 L03 uses `Nat.factorial`, which is not introduced until W19. W17's inventory says "None new." This means either (a) W17 L03 cannot be authored as specified, or (b) factorial must be introduced before W17. **Fix**: Either move `Nat.factorial` and `Nat.factorial_zero`/`Nat.factorial_succ` to W17's inventory (making W17 the introduction point and W19 a retrieval/deepening), or remove the factorial level from W17 and replace with a pure product identity.

2. **Inclusion-exclusion has no supported practice stage**: The closure table claims W13 is both supported practice and unsupported retrieval, but W13 is a pset (no scaffolding by definition). Inclusion-exclusion is introduced in W09 L06 and immediately jumps to unsupported retrieval in W13. **Fix**: Add a supported-practice level using inclusion-exclusion in W11 or W12 (where cardinality of a composite type could be computed via inclusion-exclusion as an alternative to card_prod), or add a level in W10 that uses inclusion-exclusion in a new context with hints.

### P1 (high — significant gaps):

3. **Double counting / pigeonhole coverage is weak**: Both are introduced and practiced within only W26-W27. The plan acknowledges this (Risk 7) and proposes adding a PsetCounting world, but the current plan does not include it. These are core items in the coverage map (#10). **Recommendation**: Add W26b (PsetCounting) between W26 and W27, or add double-counting and pigeonhole practice levels into W23 (PsetCombinatorics).

4. **"Choose element from nonempty finset" (core move) absent**: The coverage map lists this as a core proof move. The plan never teaches `Finset.Nonempty` → witness extraction. This move is used in pigeonhole arguments and real-world Lean proofs. **Recommendation**: Add this to W05 or W09 as a level.

5. **W25 has two centers of gravity**: Finsupp and Matrix are unrelated topics sharing one world. This violates the "each world covers one theorem family" principle. The plan acknowledges this risk. **Recommendation**: Either split into two worlds, or merge Matrix into W03/W12 (where `Fin n → α` is already taught, and `Matrix` is just `Fin m → Fin n → α`), keeping Finsupp as a standalone light world.

### P2 (medium — improvements):

6. **`simp` with Finset lemmas never taught**: A pervasive real-Lean skill. Consider a level in W08 or W13 that re-enables `simp` and teaches `simp [Finset.mem_insert, Finset.mem_union]` as a consolidation move.

7. **`calc` blocks not introduced**: Listed as core LEAN item. Useful for multi-step big-operator proofs (Phase 4) and cardinality chains. Consider introducing in W09 or W15.

8. **`ℕ not Fintype` counterexample missing**: Add a brief note or warning in W11 intro.

9. **List→Multiset→Finset supported practice compressed into W10**: Introduction and supported practice are the same world. Consider adding a retrieval level earlier in W13 that requires choosing the right abstraction layer, or adding a level in W14 that connects `Finset.sum` to `Multiset.sum`.

10. **Branching structure undocumented**: Phases 3 and 4 can be done partially in parallel (W14 depends on W06, not on any Phase 3 world), but the numbered phases suggest linear order. Document the actual dependency graph for implementers.

---

## Specific Recommendations (ranked)

1. **(P0)** Move `Nat.factorial` introduction to W17 or earlier. Change W17 from "Example (no new inventory)" to "Example (introduces factorial)". Update the closure table accordingly. Alternatively, replace W17 L03 with a product identity that doesn't use factorial.

2. **(P0)** Add inclusion-exclusion practice with scaffolding somewhere between W09 and W13. Best candidate: a level in W12 (CountingTypes) that computes `card (A ∪ B)` for concrete finsets using inclusion-exclusion, connecting abstract card_* to concrete numbers.

3. **(P1)** Add a PsetCounting world (W26b) with 5-6 levels practicing bijective proofs, pigeonhole, and double counting on fresh problems before the Finale. This gives these core techniques the supported practice → retrieval → transfer cycle they currently lack.

4. **(P1)** Add a `Finset.Nonempty` → witness level in W05 (after empty set) or in W09 (during cardinality, where nonemptiness matters for bounds).

5. **(P1)** Split W25 into W25a (Finsupp, 4 levels) and W25b (Matrix, 4 levels), or merge Matrix levels into W12 (CountingTypes) as a "matrices are just tuples of tuples" example.

6. **(P2)** Add one `simp`-with-Finset-lemmas level in W08 or W13.

7. **(P2)** Introduce `calc` blocks in W09 or W15 where multi-step equational reasoning is natural.

8. **(P2)** Document the world dependency graph as a DAG, not just a linear phase list.

---

## Overall Verdict: FAIL

The plan is impressive in scope, detail, and pedagogical care. The coverage closure table, boss map, transfer plan, inventory release plan, misconception plan, and risk analysis are all substantially above average. Most of the 27 worlds are well-designed with clear centers of gravity and proper skill seeding.

However, two issues trigger FAIL criteria:

1. **World graph dependency error**: `Nat.factorial` is used in W17 before its introduction in W19. This is a concrete authoring blocker.
2. **Core item with weak closure**: Double counting (core item #10 in the coverage map) has all five coverage stages compressed into two worlds (W26-W27). Inclusion-exclusion (part of core item #4) has no supported practice stage.

Both are fixable. Recommendation 1 fixes the dependency error. Recommendations 2 and 3 fix the closure gaps. After these three changes, the plan should pass.
