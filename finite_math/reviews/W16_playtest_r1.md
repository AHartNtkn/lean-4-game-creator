# W16 BigOpAdvanced — Playtest Audit R1

## 1. Overall Verdict

**FAIL — requires structural rework before R2.**

The world has clean compilation, correct proofs, good hint layering on most levels, and a well-structured progression from filtering through reindexing. However, three blocking issues prevent a pass:

1. The **boss does not integrate the world's content**. It uses `conv` + algebra from W15 but skips filtering (L01-L02), splitting (L03), `sum_comm` (L04), `gcongr` (L06), and reindexing (L07-L08). This is a fake boss (failure taxonomy #8).
2. The boss relies on **three untaught items** (`congr`, `Finset.sum_const`, `smul_eq_mul`), making it a lottery boss (failure taxonomy #9) layered on top of the fake boss problem.
3. `Finset.sum_le_sum` is a **one-shot exploit** on L06 that completely bypasses `gcongr`.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Plan's `sum_ite` (M38 S) missing; `sum_const`/`smul_eq_mul` never taught; filtering/reindexing not integrated in boss |
| 2. Granularity fit | 3 | L01-L08 each isolate one lesson well; L07 borderline broad (new API + 5-obligation shape) |
| 3. Proof-move teaching | 3 | `conv` pattern taught well; `gcongr` pattern taught well; reindexing 5-obligation shape well demonstrated |
| 4. Inventory design | 2 | `congr`, `sum_const`, `smul_eq_mul` used in boss without NewTheorem/NewTactic; build warnings for 8 items |
| 5. Hint design | 3 | Layered hints on all levels; boss hints guide every step; L07/L08 hint every subgoal |
| 6. Progression | 1 | Boss fails as integration — it's a W15 continuation, not a W16 capstone |
| 7. Mathematical authenticity | 3 | Good transfer sections; LaTeX formulas in intros; connections to paper math |
| 8. Paper-proof transfer | 3 | L01, L03, L04, L08 have explicit transfer sections; L05 explains conv has no paper analogue |
| 9. Technical fit | 3 | Builds clean; DisabledTactic on all 9 levels; world file correct |

**Average: 2.6 — below the 3.0 threshold. Categories 4 and 6 are below 2.**

---

## 3. Coverage Gaps

### P0: Boss does not integrate world content

The boss (L09) uses:
- `conv` (L05)
- `sum_add_distrib` (from W15)
- `mul_sum` (from W15)
- `congr 1` (UNTAUGHT)
- `Finset.sum_const` (UNTAUGHT)
- `smul_eq_mul` (UNTAUGHT)

The boss does NOT use:
- `sum_filter` (L01)
- `sum_filter_add_sum_filter_not` (L02)
- `sum_range_add` (L03)
- `sum_comm` (L04)
- `gcongr` (L06)
- `sum_nbij'` / reindexing (L07-L08)

**None of the world's six new theorems and one of its two new tactics appear in the boss.** The boss is effectively a W15 continuation exercise with `conv`.

### P1: `sum_ite` from plan not implemented

The plan specifies L2 as "`sum_ite`: Split a sum by a conditional" (coverage M38 S). The actual L02 teaches `sum_filter_add_sum_filter_not` instead. `Finset.sum_ite` does not appear anywhere in the codebase.

### P1: `Finset.sum_const` and `smul_eq_mul` never introduced

These are used in the boss (L09) in the proof `rw [Finset.sum_const, Finset.card_range, smul_eq_mul]` but were never introduced via `NewTheorem` in any world. The plan attributes them to W15 but W15 does not teach them.

### P1: `congr` tactic never introduced

`congr 1` is used in the boss but `congr` was never introduced via `NewTactic`. `gcongr` was introduced in L06, but `congr` and `gcongr` are different tactics with different purposes.

### P2: Build warnings for 8 items

The build output warns about items required by BigOpAdvanced but never introduced:
- `Finset.mem_range` (used in L07/L08 but introduced in L07 via `NewTheorem Finset.mem_Ico` — `mem_range` itself is missing)
- `congr`
- `Even`
- `arg` (conv sub-command)
- `Finset.sum_const`
- `conv_lhs` (variant of `conv`)
- `smul_eq_mul`
- `sq`

---

## 4. Granularity Defects

### P2: L07 borderline overbroad

L07 introduces `sum_nbij'` with a 5-obligation proof structure on a concrete example. This is the learner's first exposure to both the API and the multi-obligation shape. The level is long (94 lines of proof + hints) with 5 subgoals. The concrete numbers (range 4, Ico 5 9) help, but the learner faces:
- A new theorem (`sum_nbij'`) with complex signature
- A new proof shape (5 obligations after `apply`)
- New membership lemmas (`mem_Ico`, `mem_range` used with `simp only`)
- Arithmetic via `omega`

Recommendation: Consider adding a preliminary level that demonstrates the multi-obligation `apply` pattern on a simpler API, or split L07 into two: one that sets up the bijection (just the `apply` + first two membership goals) and one that completes the inverse + function-value goals.

### P3: L01-L04 are one-step levels

L01, L02, L03, L04 each have a single proof step (`rw` or `exact`). While each teaches a distinct lemma, four consecutive one-step levels may feel repetitive. This is acceptable for a lecture world but should be noted.

---

## 5. Learner Simulation

### Attentive Novice

**First likely stuck point**: L07, after `apply Finset.sum_nbij' (· + 5) (· - 5)`. The novice sees 5 goals and may panic. The intro explains the structure, but the jump from "one-step levels" (L01-L04) to "five-subgoal proof" is steep.

**Most likely wrong move on L07**: Trying to provide all 5 arguments inline to `sum_nbij'` instead of using `apply` and solving subgoals. The intro guides toward `apply` but doesn't warn against inline attempts.

**Hint rescue quality**: Good. Every subgoal in L07/L08 has both a visible strategy hint and a hidden code hint. The boss (L09) has hints at every step. The hints for L09 effectively teach `congr 1`, `sum_const`, and `smul_eq_mul` in situ, which is why the hidden prerequisite leak is partially masked — but a hint teaching new material in a boss is still a structural problem.

**Legibility of lessons**: L01-L06 are clear. Each has a single dominant lesson with good explanation. L07-L08 are heavier but the concrete-then-general progression helps.

**L09 boss**: The novice will be entirely hint-dependent. The boss introduces 3 new items (`congr 1`, `sum_const`, `smul_eq_mul`) that the novice has never seen. Even with hints, the novice is learning rather than integrating, which defeats the boss's purpose.

### Experienced Lean User

**Avoidable friction**: None of the one-step levels (L01-L04) have alternative proof paths blocked. An experienced user who knows `Finset.sum_le_sum` can bypass L06 entirely. An experienced user who knows `congr` + `ext` + `ring` can bypass L05.

**Specific exploits**:

| Level | Exploit | Severity | Notes |
|-------|---------|----------|-------|
| L05 | `congr 1; ext i; ring` | P2 | Bypasses conv entirely; ring is available from W15 |
| L05 | `simp only [sq]` | P2 | One-shot bypass |
| L05 | `norm_num [sq]` | P2 | One-shot bypass |
| L05 | `Finset.sum_congr rfl (fun i _ => by ring)` | P2 | Library lemma path |
| L06 | `exact Finset.sum_le_sum h` | P0 | One-shot bypass of gcongr, the level's entire lesson |

**Alias gaps**: The world introduces `conv` but `conv_lhs`/`conv_rhs` are used without separate documentation. An experienced user would expect these to be documented or at least listed as aliases.

**Inventory clutter**: The world introduces 8 new theorems and 2 new tactics across 9 levels. This is a high rate. The theorems are all in the "Finset" tab, which helps organization.

---

## 6. Boss Integrity Notes

### L09 Boss: FAIL

**Seeded subskills**: The boss uses `conv` (seeded in L05) and `sum_add_distrib`/`mul_sum` (seeded in W15). These are the only seeded items. `congr`, `sum_const`, and `smul_eq_mul` are NOT seeded.

**Closure quality**: Poor. The boss has 3 untaught items.

**Integration quality**: Very poor. The boss integrates nothing from L01-L04 (filtering, splitting, double sums) or L06-L08 (gcongr, reindexing). It is a `conv` + algebra exercise, not an integration of the world's content.

**Surprise burden**: High. The learner encounters `congr 1` (new tactic), `sum_const` (new theorem), and `smul_eq_mul` (new theorem) for the first time in the boss.

**Could a learner explain why the proof works?** Partially. The algebra is natural (split inner sum, distribute, factor out constant). But the Lean-specific steps (`congr 1`, `sum_const`, `smul_eq_mul`) would be opaque to a learner who only knows what this world taught.

### Recommendation: Redesign the boss

The boss should integrate the world's signature content. A good boss for this world would require:
- Filtering or splitting by predicate (L01-L02)
- Possibly range splitting (L03) or sum commutativity (L04)
- `conv` for binder-level rewrites (L05)
- `gcongr` for an inequality step (L06)
- Possibly reindexing (L07-L08)

Example boss structure: "Given a sum, split it by a predicate, reindex one part, prove an inequality on the other part using `gcongr`, then recombine." This would actually test the world's repertoire.

Additionally, `sum_const`, `smul_eq_mul`, and `congr` should be taught before the boss if they are needed. Either:
- Add levels teaching these items before the boss, or
- Redesign the boss to avoid needing them entirely.

---

## 7. Technical Risks

1. **Build warnings**: 8 items flagged as required but not introduced. These should be resolved by adding appropriate `NewTheorem`/`NewTactic` declarations or by introducing them in prerequisite worlds.

2. **`simp only` availability**: `simp` is disabled but `simp only` is available. The proofs in L07/L08 rely on `simp only` for membership simplification. This is pedagogically appropriate (explicit lemma application) but should be noted — `simp only` is never formally introduced.

3. **`omega` not disabled**: `omega` is used intentionally in L07/L08 for arithmetic but is also available on all other levels. No exploit risk identified (tested: `omega` cannot close L01-L06 or L09).

4. **`norm_num` not disabled**: `norm_num [sq]` closes L05. Consider adding `norm_num` to DisabledTactic on L05, or accept as P2 since `sq` is an untaught lemma argument.

---

## 8. Ranked Patch List

### P0 (Blocking)

1. **Redesign L09 boss to integrate world content.** The current boss is a fake boss (taxonomy #8) that integrates from W15 instead of W16. It must use filtering/splitting (L01-L03), `sum_comm` (L04), and/or reindexing (L07-L08) as core moves. `gcongr` (L06) should also appear if possible.

2. **Block `Finset.sum_le_sum` on L06.** Add `DisabledTheorem Finset.sum_le_sum` to L06. Without this, the level's entire lesson (`gcongr`) can be bypassed by `exact Finset.sum_le_sum h`.

3. **Teach `congr`, `Finset.sum_const`, `smul_eq_mul` before the boss** (or redesign boss to not need them). If the boss retains any of these items, they must be introduced in dedicated levels first. Add `NewTheorem Finset.sum_const smul_eq_mul` and `NewTactic congr` in appropriate levels, with TheoremDoc/TacticDoc entries.

### P1 (High)

4. **Add a `sum_ite` level** to cover the plan's M38(S) item. The plan specifies `sum_ite` as L2; it was replaced with `sum_filter_add_sum_filter_not`. Either add `sum_ite` as a new level or explicitly document why it was omitted.

5. **Add `NewTheorem Finset.mem_range` in L07 or a predecessor.** It's used extensively in L07/L08 `simp only` calls but never introduced. Add TheoremDoc and NewTheorem.

6. **Add `NewTheorem sq` or a note about `sq` in L05.** L05 uses `← sq` but `sq` is never introduced. Add TheoremDoc for it.

### P2 (Medium)

7. **Add `norm_num` to DisabledTactic on L05** to prevent `norm_num [sq]` bypass. Alternatively, accept as a P2 since it requires knowing the untaught lemma `sq`.

8. **Consider blocking `congr`/`ext`/`ring` combination on L05** by adding `DisabledTactic ring` on L05 only. Currently `congr 1; ext i; ring` bypasses `conv` entirely. Alternatively, accept since `ring` was just taught in W15 and the learner might legitimately combine it with `congr`/`ext`.

9. **Add TacticDoc for `conv_lhs`/`conv_rhs`** or note them as variants in the `conv` TacticDoc. Currently `conv_lhs` is used but only `conv` is documented.

10. **Address build warnings** by adding appropriate `NewTheorem`/`NewTactic`/`NewDefinition` for `Even`, `arg`, `conv_lhs`.

### P3 (Low)

11. **L07 could benefit from a scaffolding level** that introduces the 5-obligation pattern on a simpler example before the full `sum_nbij'` proof.

12. **Consider whether L01-L04 need more challenge.** Four consecutive one-step levels may feel too easy for an advanced world. This is acceptable for a lecture world but could be enriched with a follow-up practice level after L02 or L04.

---

## 9. What to Playtest Again After Patching

After implementing the P0 and P1 fixes:

1. **The new boss** — verify it actually integrates world content and all subskills are seeded.
2. **L06 with `DisabledTheorem Finset.sum_le_sum`** — verify `gcongr` is now the only viable path.
3. **Any new levels teaching `sum_const`/`smul_eq_mul`/`congr`** — verify they are well-scoped and have proper hints.
4. **The `sum_ite` level** (if added) — verify it complements L01 without redundancy.
5. **Full world build** after all changes.

---

## Summary of Blocking Issues

| # | Issue | Type | Levels |
|---|-------|------|--------|
| 1 | Boss integrates W15, not W16 | Fake boss (#8) | L09 |
| 2 | Boss uses 3 untaught items | Hidden prereq (#1) + Lottery boss (#9) | L09 |
| 3 | `Finset.sum_le_sum` one-shots L06 | Statement exploitability | L06 |
