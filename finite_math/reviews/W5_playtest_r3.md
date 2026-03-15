# W5 FinsetConstructors -- Playtest Audit Round 3

## Changes since R2

- **L08 CardinalityPeeling added** as a new practice level between L07 and the boss. Introduces `Finset.card_insert_of_notMem` and the peeling pattern. The learner practices `rw [Finset.card_insert_of_notMem h]` followed by `decide` before encountering the same pattern in the boss.
- **Boss (now L09)** uses `card_insert_of_notMem` + `card_singleton` for the cardinality conjunct. The boss proof now requires three distinct rewrites for cardinality (two `card_insert_of_notMem` and one `card_singleton`) rather than being a single `decide`.
- Level count increased from 8 to 9.

## Focus of this round

Per instructions: verify DisabledTactic on all 9 levels, no lottery moves in boss, no one-shot exploits.

---

## 1. Overall verdict

**Conditional pass.** The structural improvements from R2 are real: L08 successfully seeds the peeling pattern before the boss, and the boss now requires multi-step cardinality reasoning. The `decide` consistency issue (only enabled on L07/L08 where needed) is well-motivated. However, two systemic exploit paths remain: `norm_num` is not disabled on any level (closes L02, L05, L08, and the entire boss), and `rfl` one-shots the boss (all three conjuncts, including the cardinality goal `{1,2,3}.card = 3`). The `norm_num` gap is fixable; the `rfl` gap is a known P2 limitation. The world is clean enough to ship after adding `norm_num` to DisabledTactic.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Core construction items introduced and practiced. `card_insert_of_notMem` now has a dedicated practice level (L08) before the boss. `Finset.singleton` still lacks `NewDefinition`/`DefinitionDoc` (R2 enrichment #1). |
| Granularity fit | 3+ | Each level has one clear lesson. L08 is a well-placed practice level that fills the R1 gap (P2-3: no `card` practice between L02 and boss). World has 9 levels -- appropriate for the content. |
| Proof-move teaching | 3 | `rw` with named lemma is taught in L02, L05, L08. `use` + `decide` in L07. Boss exercises `constructor`, `rfl`, `rw [cons_eq_insert]`, `rw [card_insert_of_notMem]`, `rw [card_singleton]` -- a genuine multi-move integration. |
| Inventory design | 3 | Items unlocked at appropriate times. `card_insert_of_notMem` added to inventory at L08. `Finset.singleton` still missing from inventory (see coverage closure). |
| Hint design | 3 | Layered hints throughout. L08 has step-by-step hints at each phase. Boss has per-conjunct hints with hidden code layers. |
| Progression | 3 | L01-L06 ramp is smooth. L07 (Finset vs Set / Nonempty) is slightly off-theme but defensible (R2 enrichment #3 accepted it). L08 fills the practice gap well. Boss integrates L02-L05 and L08 skills. |
| Mathematical authenticity | 3 | Good treatment of `DecidableEq`, notation desugaring, construction hierarchy. Transfer sections in conclusions. |
| Paper-proof transfer | 3 | Every level has "In plain language" sections. L09 conclusion has a substantive transfer section. |
| Technical fit | 3- | Builds cleanly. `decide` policy is consistent (enabled only where needed). But `norm_num` is never disabled and closes most goals -- fixable. |

**Average: 3.0.** Meets threshold if `norm_num` is added to DisabledTactic.

## 3. Coverage gaps

| Item | Status | Issue |
|------|--------|-------|
| `Finset.singleton` (formal definition) | Missing | Never formally introduced via `NewDefinition`. Learner uses `card_singleton` but never sees `singleton` in inventory. R2 enrichment #1 -- still open. |
| `Finset.card_empty` | Mentioned in prose, not in inventory | L02 conclusion references it by name but no `NewTheorem` or `TheoremDoc`. R2 enrichment #7 -- still open. |
| `card_insert_of_notMem` practice | **Fixed** | L08 now provides dedicated practice. R1 P2-3 resolved. |
| `cons_eq_insert` practice | Adequate | L05 introduces, boss retrieves. Only one pre-boss use, but the boss hints guide the learner through it. |

No new coverage gaps introduced.

## 4. Granularity defects

### G1. L07 goal/narrative alignment (P2, downgraded from R1 P1)

L07's intro discusses Finset vs Set, but the goal is `Finset.Nonempty`. The R2 enrichment review accepted this as defensible with improved prose. The prose improvement is real: the intro now shows a `Set.mem_union` type error, and the conclusion explicitly connects `Finset.Nonempty` to `Set.Nonempty`. The gap is smaller than in R1.

**Status**: Acceptable. No action needed this round.

### G2. Boss is still a conjunction of independent parts (P2, downgraded from R1 P1)

The three conjuncts can still be solved independently via `constructor`. However, the cardinality conjunct now requires multi-step reasoning (`card_insert_of_notMem` twice + `card_singleton`), which is genuine integration of L02/L08 skills. The boss is no longer a gauntlet in the same sense as R1 -- the cardinality part is a real multi-step proof. The conjunction structure is standard for a world that teaches multiple construction methods.

**Status**: Acceptable. The boss now has substantive integration in its third conjunct.

## 5. Learner simulation

### Attentive novice

**First likely stuck point**: L08 (CardinalityPeeling). The learner sees `(insert 1 {2, 3}).card = 3` and must use `rw [Finset.card_insert_of_notMem h]` with the hypothesis `h`. This is the first time a rewrite uses a hypothesis from the context (rather than a named library lemma). The hint system handles this well: the first hint asks "What lemma lets you peel off the `insert`?", and the hidden hint gives the explicit code.

**Most likely wrong move**: On L08, trying `rfl` (which works, bypassing the lesson -- see T2 below). On L09 (boss), trying `rfl` on the cardinality conjunct (also works). The novice may never learn the peeling pattern.

**Hint rescue quality**: Good throughout. L08 has appropriately layered hints at both the rewrite step and the `decide` step. Boss hints are per-conjunct with strategy-then-code layering.

**Lesson legibility**: Clear on all levels. L08's intro explains the peeling pattern with a worked example. The boss intro explicitly lists what tools are needed and from which level they come.

### Experienced Lean user

**Avoidable friction**: None. The proofs are short and the inventory is clean.

**Exploit summary**: The experienced user can `rfl` the entire boss in one step (`exact ⟨rfl, rfl, rfl⟩`). They can `norm_num` through L02, L05, and L08. They can `decide` through L07 and L08 (where it is enabled). The world teaches them nothing if they use these shortcuts.

**Inventory clutter**: None. Items are introduced cleanly.

## 6. Boss integrity notes (L09)

### Seeded subskills
- `rfl` for definitional equality: L01, L03, L04, L06. Fully seeded.
- `constructor` for conjunctions: Assumed from NNG4. Standard.
- `rw [Finset.cons_eq_insert]`: L05. One pre-boss use. Adequate with hints.
- `rw [Finset.card_insert_of_notMem h]`: **L08 (NEW)**. Dedicated practice level before boss. Fully seeded.
- `rw [Finset.card_singleton]`: L02 (used with `rw`). One pre-boss use. Adequate.

### Closure quality
All boss subskills are taught and practiced before the boss. The R1 gap (no `card` practice between L02 and boss) is resolved by L08.

### Integration quality
The cardinality conjunct (part 3) genuinely integrates L08's `card_insert_of_notMem` with L02's `card_singleton` in a multi-step rewrite chain. The `cons` conjunct (part 2) uses a double `rw [cons_eq_insert]`. These are real multi-step proofs. The first conjunct (notation = explicit insert) is `rfl` -- trivial but pedagogically appropriate as a warm-up.

### Lottery moves
**None.** All boss moves are taught. No untaught micro-skills. This was the R1 P0 issue; the redesigned boss has no lottery moves.

### Surprise burden
**None.** The longest sub-proof in the boss (cardinality: 3 rewrites) is the same length as L08's proof. No scale surprise.

### Can the learner explain why the proof works?
If the learner follows the intended path: "The three construction methods produce the same finset because notation desugars to `insert` chains, and `cons` converts to `insert` via `cons_eq_insert`. The cardinality is 3 because each `insert` adds a new element (proved by non-membership hypotheses), so we peel off two inserts (+1 each) and the singleton has cardinality 1."

This is a meaningful explanation. The boss achieves its pedagogical goal *when the intended proof is followed*.

## 7. Technical risks

### T1. `norm_num` not disabled (P1)

`norm_num` is absent from every DisabledTactic line in the world. Testing confirms it closes:
- L02: `norm_num` closes `({5} : Finset Nat).card = 1`
- L05: `norm_num` closes `Finset.cons 1 {2} h = {1, 2}`
- L08: `norm_num` closes `(insert 1 {2, 3}).card = 3`
- L09 (boss): `refine ⟨?_, ?_, ?_⟩ <;> norm_num` closes all three conjuncts

This is the single most impactful exploit in the world. Adding `norm_num` to every DisabledTactic line is a one-line change per file, and it eliminates the bypass path on 4 out of 9 levels plus the boss.

**Fix**: Add `norm_num` to DisabledTactic on all 9 levels.

### T2. `rfl` closes the entire boss and most levels (P2, known limitation)

`exact ⟨rfl, rfl, rfl⟩` still closes the boss. Testing confirms:
- `({1, 2, 3} : Finset Nat).card = 3` is definitionally true (`rfl` closes it)
- `Finset.cons 1 (Finset.cons 2 {3} h₁) h₂ = {1, 2, 3}` is definitionally true
- The notation-desugaring conjunct is obviously `rfl`

Cannot disable `rfl`. This is the known P2 limitation from project lessons learned. The `rfl` bypass is inherent to Lean's definitional reduction on concrete `Finset Nat` values.

**Mitigation**: Accept. The hints guide toward the intended proof. The `rfl` bypass requires the learner to *know* that `rfl` works here, which is itself some understanding. A Branch hint saying "That works! But the intended approach uses structural lemmas..." could be added (P3).

### T3. L08 `decide` bypass (P2)

L08 has `decide` enabled (to close the residual `{2,3}.card + 1 = 3` after the rewrite). But `decide` also closes the entire goal one-shot: `(insert 1 {2, 3}).card = 3` is decidable. The learner can skip the `card_insert_of_notMem` lesson entirely.

The `decide` enablement is intentional (needed for the second step of the intended proof). The one-shot bypass is a side effect.

**Mitigation**: Accept as P2. The hint system guides toward the two-step proof. The novice will likely try the hints before trying `decide` on the full goal. The experienced user who tries `decide` first already knows cardinality is decidable.

### T4. L07 `decide` one-shot (P2, known)

L07 has `decide` enabled to close the membership sub-goal after `use 1`. But `decide` also closes `Finset.Nonempty {1,2,3}` directly, bypassing the `use` step.

**Mitigation**: Accept as P2. This was flagged in R1 as P1 and the R2 enrichment review marked the `decide` policy as "Resolved." The pedagogical choice is defensible: the level teaches `use`, and the hint system guides toward `use 1; decide`. A learner who discovers the `decide` one-shot has at least learned that `Nonempty` is decidable.

### T5. Build status
The world compiles. No build errors or warnings specific to W5 (systemic "Missing Tactic Documentation" warnings from earlier worlds are unrelated).

### T6. DisabledTactic consistency check

| Level | trivial | decide | native_decide | simp | aesop | simp_all | norm_num |
|-------|---------|--------|---------------|------|-------|----------|----------|
| L01 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L02 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L03 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L04 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L05 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L06 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |
| L07 | Yes | No* | Yes | Yes | Yes | Yes | **No** |
| L08 | Yes | No* | Yes | Yes | Yes | Yes | **No** |
| L09 | Yes | Yes | Yes | Yes | Yes | Yes | **No** |

*L07/L08: `decide` intentionally enabled for their proof goals.

The `decide` policy is consistent and well-motivated. The `norm_num` omission is the only systemic gap.

## 8. Ranked patch list

### P1 (high)

**P1-1. Add `norm_num` to DisabledTactic on all 9 levels.**
`norm_num` closes L02, L05, L08, and all three boss conjuncts. It is the only automation tactic that (a) is not disabled, (b) bypasses dominant lessons on multiple levels, and (c) is easily fixable. One-line change per file.

### P2 (medium)

**P2-1. `rfl` closes the entire boss (known limitation).**
Cannot disable `rfl`. Accept. Consider adding a Branch hint on the boss's cardinality conjunct: "Nice -- `rfl` works because Lean can compute this definitionally. The structural approach using `card_insert_of_notMem` generalizes to non-literal finsets."

**P2-2. `decide` closes L08 one-shot (side effect of intentional enablement).**
Accept. The `decide` enablement is needed for the second step. The hint system guides toward the intended two-step proof.

**P2-3. `decide` closes L07 one-shot (side effect of intentional enablement).**
Accept. Same reasoning as P2-2.

### P3 (low)

**P3-1. `Finset.singleton` and `Finset.card_empty` inventory gaps (from R2 enrichment).**
Not blocking for this audit. Should be addressed in the enrichment cycle.

## 9. What to playtest again after patching

After adding `norm_num` to DisabledTactic on all 9 levels:

1. **Build**: Run `lake build` to confirm compilation.
2. **L02, L05, L08**: Verify `norm_num` is now blocked and the intended proof (`rw` + lemma) is the primary path (with `rfl` as the unavoidable alternative).
3. **L09 (Boss)**: Verify `norm_num` is blocked. Confirm `exact ⟨rfl, rfl, rfl⟩` still works (it will -- `rfl` cannot be disabled). Confirm the intended multi-step proof works.
4. **L07, L08**: Verify `decide` is still enabled and the intended proofs (`use 1; decide` and `rw [...]; decide`) work.

No re-audit should be needed after this patch unless the `norm_num` addition causes unexpected build failures (unlikely -- `DisabledTactic` is a game-server directive, not a Lean compilation directive).
