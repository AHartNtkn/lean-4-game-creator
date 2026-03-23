# Cross-World Issues: Finite Mathematics

Post-authoring analysis of all 29 worlds (498 levels). Issues ranked by severity.

---

## P0 Issues (Blocking)

**None found.**

All 10 "Core Items That Must Not Be Missed" from the coverage map are covered with strong closure:
1. `Fin n` — strong (MeetFin + FinNavigation + FinTuples + PsetFin + later worlds)
2. `Finset` — strong (FinsetBasics + FinsetOps + FinsetImage + PsetFinset + later worlds)
3. `Fintype` — strong (Fintype + CountingTypes + PsetCardinality)
4. `Finset.card` — strong (Cardinality 26L + extensive retrieval)
5. Big operators — strong (BigOpIntro + BigOpAlgebra + FinsetInduction + SummationFormulas + PsetBigOp)
6. Binomial coefficients — strong (BinomialCoefficients + Powerset + BinomialTheorem + PascalsTriangle + PsetCombinatorics)
7. Finset induction — strong (FinsetInduction + SummationFormulas + PsetBigOp)
8. List → Multiset → Finset — strong (AbstractionLadder 23L + BigOpIntro L12)
9. Proof by extensionality — strong (MeetFin L15, FinTuples L12, FinsetOps L08, Matrices L04)
10. Double counting / bijective proof — strong (CountingTechniques + PsetCounting + Finale)

---

## P1 Issues (High)

### P1-1: Level density imbalance — Powerset (27L) vs FinsetInduction (9L)

**What**: Powerset has 27 levels — the largest world in the course. FinsetInduction has 9 levels. Both teach core material of comparable difficulty. The 3:1 ratio is notable.

**Worlds affected**: Powerset (W20), FinsetInduction (W16)

**Assessment**: Powerset covers both `powerset` AND `powersetCard` with their cardinality theorems plus complement/monotonicity/involution plus concrete counting — the level count is justified by the breadth of the theorem family. FinsetInduction is tight because the proof pattern (base case + inductive step) is genuinely uniform — more levels would be repetitive, not pedagogically deeper. The density difference reflects content, not imbalance.

**Suggested fix**: No action required. The apparent imbalance is justified by the content scope of each world.

---

### P1-2: Level density imbalance — Matrices (21L) and Finsupp (17L) vs plan (5L each)

**What**: These "light lecture/example" worlds expanded 3-4× from plan. The plan called for 5 levels each. Matrices has 21 levels covering addition, transpose algebra, diagonal/diag interaction, trace as a big operator, and counterexamples. Finsupp has 17 levels covering single evaluation, support reasoning, pointwise addition, accumulation, cancellation, extensionality, and support bounding.

**Worlds affected**: Matrices (W26), Finsupp (W25)

**Assessment**: The expansion is substantive — both worlds teach genuine proof moves (matrix extensionality, trace computation, Finsupp extensionality, support algebra) that are used in the Finale. The worlds earn their size. However, at 21 and 17 levels respectively for "supporting" topics, they collectively represent 38 levels — more than Phase 1's entire lecture content (MeetFin 23L + FinNavigation 16L = 39L, but those teach core material). A learner might feel these worlds are disproportionately long relative to their advertised importance.

**Suggested fix**: No structural change needed. Consider marking optional skip points within each world (e.g., "if you're comfortable with matrix extensionality, skip to L12") to let advanced learners move faster through these worlds.

---

### P1-3: Telescoping sum has no retrieval outside SummationFormulas

**What**: Telescoping sums are introduced in SummationFormulas L12 and used in the boss (L14), but never retrieved in a later world or pset. The coverage map rates this as "supporting" but the technique has no practice outside its introduction world.

**Worlds affected**: SummationFormulas (W17), PsetBigOp (W18)

**Assessment**: The PsetBigOp world does not include a telescoping problem. Telescoping is a high-value proof technique in mathematics (it appears in analysis, number theory, combinatorics). Its absence from any pset or later world means the learner practices it exactly twice (L12 + boss) and then never again.

**Suggested fix**: Add a telescoping sum problem to PsetBigOp or PsetCombinatorics. Alternatively, if this is intentional (telescoping is truly "supporting" in scope), no action needed — but the current status means it won't transfer.

---

## P2 Issues (Medium)

### P2-1: `Finset.map` deferred but never covered

**What**: The plan explicitly deferred `Finset.map` from FinsetImage to "a later world" covering embeddings (`α ↪ β`). No such world was authored. The FinsetImage world mentions `map` in L13's conclusion for awareness, and AbstractionLadder L23's boss uses `Finset.map` in passing, but the formal embedding concept and `map_eq_image` bridge are not taught.

**Worlds affected**: FinsetImage (W07), course-wide

**Assessment**: `Finset.map` is marked as "supporting" in the coverage map. The course covers `Finset.image` thoroughly (23 levels). The `map` variant requires bundled embeddings, which is a concept that doesn't appear elsewhere in this course. Deferring it is a reasonable scope decision.

**Suggested fix**: No action needed for this course. If a future "Embeddings" course is planned, `Finset.map` and `map_eq_image` would be natural content there.

---

### P2-2: `sum_image` and `prod_image` not formally taught

**What**: Reindexing sums/products via `Finset.sum_image` and `Finset.prod_image` are listed as "supporting" in the coverage map but never appear as `NewTheorem` or as the focus of any level. The fiber decomposition theorem `card_eq_sum_card_fiberwise` is taught (CountingTechniques L11), but the more basic `sum_image` is not.

**Worlds affected**: BigOpAlgebra (W15), CountingTechniques (W27)

**Assessment**: `sum_image` is a useful lemma for reindexing sums by an injective function. Its absence means the learner cannot cleanly change summation variables. However, the course compensates with `sum_congr` for pointwise rewriting, `sum_antidiagonal_eq_sum_range_succ_mk` for antidiagonal reindexing, and `card_eq_sum_card_fiberwise` for fiber decomposition. The gap is real but narrow.

**Suggested fix**: Consider adding `sum_image` as a `NewTheorem` in BigOpAlgebra or SummationFormulas with a single supporting level. Low priority.

---

### P2-3: `norm_num` never enabled

**What**: `norm_num` is disabled throughout the entire course. The plan noted it should stay disabled through W09, with possible re-enabling in W14 (BigOperators). It was never re-enabled. `omega` is used for all numeric arithmetic.

**Worlds affected**: Course-wide

**Assessment**: This is a design choice, not a gap. `omega` covers all the natural number arithmetic in the course. `norm_num` would be useful for ring arithmetic (e.g., `2 * 3 = 6`), but `ring` handles those cases when they arise. The learner does not learn to use `norm_num`, which is a common Lean tactic, but this is acceptable for a finite mathematics course where `omega` + `ring` cover the arithmetic needs.

**Suggested fix**: No action needed. Document the decision if it might confuse users of other Lean courses.

---

### P2-4: `fin_cases` never enabled

**What**: `fin_cases` is disabled throughout Phase 1 (W01-W04) to force manual case analysis. It is never re-enabled in any later world.

**Worlds affected**: PsetFin (W04), course-wide

**Assessment**: This is an intentional design choice — the course teaches manual Fin case analysis as a proof skill. The learner never learns `fin_cases` as a shortcut, which is somewhat limiting for practical Lean usage outside this game. However, the manual technique transfers better to paper proofs.

**Suggested fix**: Consider re-enabling `fin_cases` in a late world (e.g., CountingTechniques or Finale) with a brief mention that this tactic automates the case analysis they learned to do manually. Low priority.

---

### P2-5: Supporting tactics `conv`, `suffices`, `refine` not covered

**What**: Three supporting tactics from the coverage map are never introduced: `conv` (targeted rewriting inside nested structures), `suffices` (backward reasoning), and `refine` (partial term construction with holes).

**Worlds affected**: Course-wide

**Assessment**: These are useful Lean skills but not essential for the course's mathematical content. `conv` would be helpful for rewriting inside big operators, but `sum_congr rfl (fun x hx => ...)` serves the same purpose and is taught. `suffices` is a proof organization tool; `have` covers its primary use case. `refine` is advanced and its use case (`?_` holes) doesn't arise naturally in this course.

**Suggested fix**: No action needed. These are Lean fluency items, not mathematical content. A "Lean Tactics" course could cover them.

---

### P2-6: `native_decide` taught in exactly one level

**What**: `native_decide` is introduced in FinsetImage L21 and never used again. It's introduced to demonstrate that counting can prove injectivity — a clever pedagogical point, but the tactic itself is a one-off.

**Worlds affected**: FinsetImage (W07)

**Assessment**: `native_decide` is a "nuclear" tactic that bypasses manual proof. Teaching it once to show what it can do, then not using it again, is reasonable. The pedagogical point (counting proves injectivity) is the lesson, not the tactic itself.

**Suggested fix**: No action needed.

---

### P2-7: `Finset.DecidableEq` requirement never exercised as an error

**What**: The misconception "Finset requires DecidableEq — not every type works" is listed as core but only mentioned in introductory text, never demonstrated via an actual type error or exercise.

**Worlds affected**: FinsetBasics (W05)

**Assessment**: Showing a failed attempt (e.g., trying to build a `Finset` over a type without `DecidableEq`) would concretize this misconception. The current text-only treatment may not stick.

**Suggested fix**: Consider adding a level in FinsetBasics that briefly demonstrates the `DecidableEq` requirement, perhaps showing what happens with and without it. Low priority.

---

### P2-8: `↑s` coercion Finset → Set not taught

**What**: The coercion from `Finset α` to `Set α` via `↑s` is listed as supporting in the coverage map but never explicitly taught in any level.

**Worlds affected**: Course-wide

**Assessment**: This coercion appears naturally in Lean when mixing Finset and Set APIs. Not teaching it means learners may be confused if they encounter `↑s` in the wild. However, the course works entirely within the Finset API and never needs the Set coercion.

**Suggested fix**: No action needed for this course. A "Sets and Finsets" bridge course could cover this.

---

## No Issues (Confirmed Clean)

The following areas were checked and found to have no issues:

- **Coverage drift**: All 10 core items from the coverage map are introduced, practiced, retrieved, and integrated. No core item was promised but undelivered.
- **Coverage gaps between worlds**: No theorem family was split across worlds without closure. Each world that introduces a concept provides enough practice before the pset retrieves it.
- **Redundancy**: Minimal. The Cardinality world (W09) introduces `card_product` and the Products world (W24) revisits it, but the Products world uses the full `mem_product` characterization — genuinely new demand. No other redundancy detected.
- **Boss integrity**: Every boss was checked against its world's inventory. No boss depends on an untaught micro-skill.
- **Pset quality**: Every pset world provides retrieval for its associated lecture worlds without merely cloning lecture examples. Problems are on fresh surface forms.
- **Example coverage**: All major definitions are concretized on specific objects. Key counterexamples (Fin 0 empty, image shrinks cardinality, choose n k = 0 for k > n, ℕ not Fintype, diagonal ∘ diag ≠ identity) are present.
- **World coherence**: Each world has a clear center of gravity stated in its introduction. No world mixes unrelated theorem families.
- **Dependency graph**: The 29-world dependency graph (in Game.lean) is acyclic and pedagogically sound. Each dependency is justified by content prerequisites.

---

## Summary

| Severity | Count | Action needed |
|----------|-------|---------------|
| P0 (blocking) | 0 | None |
| P1 (high) | 3 | P1-3 is the only actionable one (telescoping retrieval gap). P1-1 and P1-2 are noted imbalances that are justified on inspection. |
| P2 (medium) | 8 | All are minor. Most are supporting items intentionally omitted or design choices. |

**Overall assessment**: The course has strong coverage closure across all core items. The coverage map from Phase 1 was executed faithfully — every core MATH, MOVE, LEAN, NOTATION, MISCONCEPTION, EXAMPLE, and TRANSFER item is accounted for. The only actionable gap is P1-3 (telescoping sum not retrieved outside its introduction world). The remaining issues are either intentional design choices (norm_num disabled, fin_cases disabled, Finset.map deferred) or supporting items that were reasonably omitted.
