# W10_ps FinsetPset -- Playtest Audit R2

**World**: FinsetPset (8 levels: L01-L08, Pset)
**Round**: 2 (verifying R1 fix: `omega` disabled on L05)
**Auditor**: lean4game-playtest-auditor
**Build**: Passes (warnings only, no errors)

---

## 1. Overall verdict

**NEEDS REVISION -- 2 P0 defects, 3 P1 defects.**

The R1 fix is correct: `omega` is now disabled on L05. However, the world has a systemic `simp` omission (not disabled in any of the 8 levels) that creates P0-level exploitability on multiple levels, and several levels are closable by library lemmas or `rfl`/`norm_num` without engaging the intended lesson. The boss (L08) is fully closeable by `simp [Finset.card_union_le]` in one tactic call.

---

## 2. R1 fix verification

| R1 issue | Status | Notes |
|----------|--------|-------|
| `omega` closes L05 entirely (bypasses induction) | **FIXED** | L05 line 62: `DisabledTactic trivial decide native_decide aesop simp_all omega`. Confirmed `omega` cannot close the goal. |

---

## 3. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Items mapped to plan. Transfer levels have good paper-proof content. But `sdiff` not warmed up before boss. |
| Granularity fit | 2 | L06 and L07 are single-`exact` levels in a pset world. L05's target does not genuinely require the inductive hypothesis. |
| Proof-move teaching | 2 | Several levels can be bypassed by `simp`, `norm_num`, or library lemmas, so the intended proof move is never forced. |
| Inventory design | 3 | No new inventory introduced (correct for a pset). DisabledTactic is incomplete. |
| Hint design & recoverability | 3 | Hints are appropriately sparse for a pset. Layered (hidden). L04 hint guides toward `have` + `ext` pattern. |
| Progression (worked -> practice -> boss) | 2 | L06 and L07 are passive (one `exact` each). The boss is trivially closeable. Progression from retrieval to integration is undermined. |
| Mathematical authenticity | 3 | Transfer conclusions in L06-L07 are strong. L03 absorption law is well-motivated. |
| Paper-proof transfer | 4 | L06 and L07 conclusions provide excellent paper-proof translations. L08 conclusion has a good retrieval table. |
| Technical fit | 2 | Build passes but `simp` is not disabled in any level. Multiple exploitable statements. |

**Average: 2.7** -- below the 3.0 threshold. Two categories below 2.

**Red flags triggered:**
- Exploitable statements: L01, L02, L03, L05, L06, L07, L08 all have bypass paths
- Boss closeable by a single `simp [Finset.card_union_le]`
- Pset levels that are one-`exact` proofs (L06, L07) -- does not force retrieval

---

## 4. Technical sanity

### 4a. Build status

All 8 levels compile. Build warnings (inherited from prior worlds):
- Missing TacticDoc for `aesop`, `simp_all` (standard -- these exist in earlier worlds but build order re-emits warnings).
- "No world introducing `Finset.induction_on`", `case`, `induction`, `Insert.insert`, `Nat` -- these are W10/FinsetInduction carry-over warnings.

### 4b. DisabledTactic audit

| Level | DisabledTactic | `simp`? | `omega`? | `norm_num`? | Issues |
|-------|---------------|---------|----------|-------------|--------|
| L01 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P0**: `simp` closes goal. `norm_num [...]` also closes goal. |
| L02 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P0**: `simp [...]` closes goal after `intro a ha`. `norm_num` also closes subset. |
| L03 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P0**: bare `simp` closes `s ∩ (s ∪ t) = s`. Library lemma `inf_sup_self` also closes. |
| L04 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P2**: `rfl` closes the entire goal (concrete filter+card is definitionally true). Cannot disable `rfl`. |
| L05 | trivial decide native_decide aesop simp_all omega | NO | YES | NO | **P1**: `simp` closes goal. `norm_num` closes goal. `linarith` closes goal. `omega` correctly disabled. |
| L06 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P2**: `rfl` closes the entire goal. `norm_num` also closes. Cannot disable `rfl`. |
| L07 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P1**: `simp` closes goal (ignoring `h`). `norm_num` also closes. |
| L08 | trivial decide native_decide aesop simp_all | NO | NO | NO | **P0**: `simp [Finset.card_union_le]` closes entire boss in one tactic. |

### 4c. Statement exploitability -- detailed

| Level | Intended lesson | Exploit | Severity | Details |
|-------|----------------|---------|----------|---------|
| L01 | Membership rewriting retrieval (V5) | `simp [Finset.mem_insert, Finset.mem_singleton]` | **P0** | This IS the model proof. But `simp` alone (with auto-discovered lemmas) or `norm_num [...]` also work. With `simp` disabled, the learner must use `rw` chains or `simp only` -- genuine retrieval. |
| L02 | Subset proof retrieval (V14) | `simp [Finset.subset_iff, ...]` after intro | **P0** | `simp` closes after intro. `norm_num` closes the whole goal. |
| L03 | ext + membership reasoning (V6, V7) | bare `simp` | **P0** | `simp` closes `s ∩ (s ∪ t) = s` in one step. Also `exact inf_sup_self`. |
| L04 | Filter + cardinality retrieval (M8, M9) | `rfl` | **P2** | `rfl` closes the concrete equality. Cannot disable. Accepted (known issue with concrete finset cardinality). |
| L05 | Finset induction retrieval (V4) | `simp` / `norm_num` / `linarith` | **P1** | All three close `s.card ≤ s.card + s.card` without induction. `omega` correctly disabled. |
| L06 | Inclusion-exclusion transfer (T4) | `rfl` / `norm_num` | **P2** | Concrete equality is definitionally true. Also `exact Finset.card_union_add_card_inter _ _` is the intended one-liner. |
| L07 | Subset-cardinality transfer (T3) | `simp` / `norm_num` (both ignore `h`) | **P1** | Both close the concrete cardinality inequality without using `h` or `card_le_card`. |
| L08 | Multi-step integration (boss) | `simp [Finset.card_union_le]` | **P0** | One tactic closes all 3 parts. Also: `exact ⟨by simp, Finset.inter_subset_left, Finset.card_union_le s t⟩`. |

### 4d. Library lemma exploits (DisabledTheorem audit)

| Level | Library one-shot | Currently disabled? | Severity |
|-------|-----------------|-------------------|----------|
| L03 | `exact inf_sup_self` | NO | **P1** -- bypasses ext+membership reasoning entirely |
| L06 | `exact Finset.card_union_add_card_inter _ _` | NO | Intended -- this IS the model proof |
| L07 | `exact Finset.card_le_card h` | NO | Intended -- this IS the model proof |
| L08 Part 2 | `exact Finset.inter_subset_left` | NO | **P1** -- bypasses intro+mem_inter reasoning |
| L08 Part 3 | `exact Finset.card_union_le s t` | NO | **P1** -- bypasses inclusion-exclusion + omega reasoning |

---

## 5. Coverage sanity

### 5.1. Coverage map

| Item | Axis | Plan stage | Status | Notes |
|------|------|-----------|--------|-------|
| Membership rewriting (V5) | MOVE | T | Present (L01) | `simp` bypass undermines retrieval |
| Subset proof (V14) | MOVE | T | Present (L02) | `simp`/`norm_num` bypass available |
| `ext` for finset equality (V6) | MOVE | T | Present (L03) | bare `simp` bypass; also `inf_sup_self` one-shot |
| Membership case analysis (V7) | MOVE | T | Present (L03) | Same bypass as V6 |
| Filter reasoning (M8) | MATH | T | Present (L04) | `rfl` bypass (accepted P2) |
| Cardinality (M9) | MATH | T | Present (L04) | Same |
| Finset induction (V4) | MOVE | T | Present (L05) | `simp`/`norm_num`/`linarith` bypass; `omega` fixed |
| Inclusion-exclusion (T4) | TRANSFER | R | Present (L06) | Intended one-liner; `rfl` also works |
| Subset-cardinality (T3) | TRANSFER | I | Present (L07) | `simp`/`norm_num` bypass ignoring `h` |
| Integration (boss) | -- | G | Present (L08) | Full `simp` bypass |

### 5.2. `sdiff` not warmed up before boss

L08 Part 1 requires `Finset.mem_sdiff`. No earlier level in this pset exercises set difference. The learner's last exposure was in W7 (FinsetOperations). This is the only boss subskill without a warm-up level in this world.

Severity: **P2** -- the boss hints guide the learner to `mem_sdiff`, so recovery is possible, but the pset principle of "retrieval under reduced scaffolding" is violated for this one skill.

### 5.3. L05 induction target does not exercise `ih`

The statement `s.card ≤ s.card + s.card` is a pure Nat inequality. In the insert step, after rewriting with `card_insert_of_notMem ha`, the goal becomes `s'.card + 1 ≤ (s'.card + 1) + (s'.card + 1)`, which is true regardless of `ih`. The learner can close this with `omega` (now disabled), but also with `norm_num`, `linarith`, or `simp`. Even with all automation disabled, the learner would not need `ih`. This makes L05 a syntax drill ("type `induction s using Finset.induction_on`") rather than genuine retrieval of the full induction pattern.

Severity: **P2** -- the induction skeleton is practiced, but the inductive hypothesis is dead weight. The enrichment reviewer (R1 and R2) flagged this independently. The retrieval value is significantly weakened.

---

## 6. Granularity sanity

### 6a. Level assessment

| Level | Role | Dominant lesson | Granularity | Notes |
|-------|------|----------------|-------------|-------|
| L01 | Retrieval | Membership rewriting (V5) | OK | Fresh finset, same technique. |
| L02 | Retrieval | Subset proof (V14) | OK | Fresh finset pair, same pattern. |
| L03 | Retrieval | ext + membership (V6, V7) | OK | Absorption law is a genuinely fresh identity. |
| L04 | Retrieval | Filter + cardinality (M8, M9) | OK | Multi-step proof (have + rw + rfl). |
| L05 | Retrieval | Finset induction (V4) | Weak | Target does not require `ih`. |
| L06 | Transfer | Inclusion-exclusion (T4) | Thin | Single `exact`. Value is in conclusion, not proof. |
| L07 | Transfer | Subset-cardinality (T3) | Thin | Single `exact`. Value is in conclusion, not proof. |
| L08 | Boss | Multi-step integration | OK in concept | But trivially closeable by `simp [Finset.card_union_le]`. |

### 6b. Pset integrity

This is a pset world. Required checks:

- **Fresh surface form**: L01 (new finset), L02 (new finset pair), L03 (absorption law, genuinely new identity), L04 (new filter predicate + finset), L05 (new induction target). Fresh surface is present but sometimes shallow (L01, L02 are "same proof, different numbers"). **P2**.
- **Reduced scaffolding**: Hints are hidden. Introductions give less guidance than lecture levels. This is appropriate. **Pass**.
- **Real retrieval**: Undermined by `simp` availability. The learner can solve L01-L03, L05, L07, L08 using `simp` without recalling specific lemma names. **P0** when simp is enabled.
- **More than cloning lecture material**: L03 (absorption law) and L04 (filter+card) are genuinely new. L01, L02, L06, L07 are structurally identical to lecture levels with different constants. **P2** -- borderline for L06/L07 (transfer levels are allowed to be one-liners since value is in the conclusion).

### 6c. Boss integrity (L08)

- **Seeded subskills**: `mem_sdiff` (W7, but NOT in this pset before boss -- gap), `mem_inter` (L03 exercises it), `Finset.card_union_add_card_inter` (L06), `inter_subset_left` pattern (L02, L03). All present in the course, but `sdiff` skips the warm-up in this world.
- **Closure quality**: The boss statement decomposes into three independent parts with no interaction. Each part is a standalone exercise. This is a gauntlet, not an integration. The parts do not interact or build on each other.
- **Integration quality**: Weak. `refine ⟨?_, ?_, ?_⟩` splits the problem and then each part is solved independently. The learner never needs to see the whole structure. The `simp [Finset.card_union_le]` one-shot confirms the boss lacks genuine integration demand.
- **Surprise burden**: Low (when not exploited). The intro explains the three parts clearly.
- **Can learner explain why the proof works?**: Yes -- the conclusion provides a clear retrieval table and transfer moment.

**Boss verdict**: The boss is a gauntlet (failure taxonomy #8b). Three independent parts solved in sequence with no novel interaction. The `simp` one-shot proves this: if one tactic can close all three parts, the boss has no structural complexity. After `simp` is disabled, the boss becomes three independent exercises separated by `refine ⟨?_, ?_, ?_⟩`, which is better but still lacks a planning challenge.

---

## 7. Learner simulation

### 7a. Attentive novice

**First likely stuck point**: L04. The learner must realize that the filter of `{2, 4, 6, 8, 10}` by `x > 5` produces `{6, 8, 10}`. This requires either:
- A `have` statement with the exact result and a proof via `ext` + `mem_filter` + `omega`, OR
- Knowing to try `rfl` (which works since the computation is definitional).

The hidden hint guides toward the `have` approach, which involves a 3-step inner proof (`ext x`, `simp only [...]`, `omega`). A novice will find this challenging but the hint covers each step.

**Most likely wrong move**: In L03, trying `rw [Finset.inter_comm]` or `rw [Finset.union_comm]` before `ext`, because the statement looks like it should simplify algebraically. The hints guide toward `ext` first, but the novice may not realize why extensionality is needed before rewriting.

**Hint rescue quality**: Good. Hints are hidden (reduced scaffolding, appropriate for pset). Each level has at least one hidden hint with the key step. L08 has hints for each of the three parts.

**Lesson legibility**: Clear. Each introduction states what is being retrieved and from where.

### 7b. Experienced Lean user

**Avoidable friction**: The experienced user will immediately try `simp` on L01-L03 and succeed. They will try `norm_num` or `rfl` on L04, L06, L07 and succeed. The boss yields to `simp [Finset.card_union_le]`. The experienced user completes the entire pset in under 2 minutes without any meaningful retrieval. This is a **critical failure of the pset design** when `simp` is available.

**Alias gaps**: None detected. The lemma names used are standard mathlib names.

**Inventory clutter**: None. No new inventory introduced (correct for pset).

**Needless forced verbosity**: L04's `have` + `ext` + `simp only` + `omega` chain is the longest proof. With `simp` disabled, this is appropriate difficulty for a pset.

---

## 8. Course-role sanity

| Level | Intended role | Actual role | Match? |
|-------|-------------|-------------|--------|
| L01 | Pset retrieval | Exploitable by `simp` -- acts as a worked example | NO (when `simp` enabled) |
| L02 | Pset retrieval | Exploitable by `simp` -- acts as a worked example | NO (when `simp` enabled) |
| L03 | Pset retrieval | Exploitable by `simp` or `inf_sup_self` -- acts as a one-liner | NO |
| L04 | Pset retrieval | `rfl` closes it, but `rfl` cannot be disabled. With `rfl` knowledge aside, the `have` path is genuine retrieval | Partial |
| L05 | Pset retrieval | Exploitable by `simp`/`norm_num`/`linarith`; even with those disabled, `ih` is unnecessary | NO |
| L06 | Pset transfer | One `exact` -- passive transfer (conclusion is the real content) | Marginal |
| L07 | Pset transfer | One `exact` -- passive transfer (conclusion is the real content) | Marginal |
| L08 | Pset boss | `simp [Finset.card_union_le]` one-shot; gauntlet structure | NO |

---

## 9. Ranked patch list

### P0 (blocking -- must fix)

**P0-1: Add `simp` to DisabledTactic in ALL 8 levels.**

Currently every level disables `trivial decide native_decide aesop simp_all` but NOT `simp`. `simp` closes L01, L02, L03, L05, L07, and L08 entirely (bypassing the intended lesson in each case). The standard disabled set for this course is `trivial decide native_decide simp aesop simp_all`.

**Fix**: Add `simp` to the DisabledTactic line in every level. Then update model proofs:
- L01: Replace `simp [Finset.mem_insert, Finset.mem_singleton]` with `rw`/`simp only` equivalent or use `Finset.mem_insert.mpr` chains.
- L02: Replace `rcases ha with rfl | rfl <;> simp` with explicit `Finset.mem_insert.mpr` or `simp only` steps.
- L04: Replace `simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]` (inside `have`) with same but ensure `simp only` is not also disabled. (`simp only` should remain enabled since it requires explicit lemma arguments and does not auto-discover.)
- L08 Part 1: Replace `simp [Finset.mem_insert, Finset.mem_singleton]` lines with `rw`/`simp only` equivalents.

**Why it matters**: This is a pset world whose purpose is retrieval under reduced scaffolding. With `simp` enabled, the learner can solve 6 of 8 levels without recalling any specific finset lemma. This defeats the entire purpose of the world.

**P0-2: Add `norm_num` to DisabledTactic in L01, L02, L05, L07, L08.**

`norm_num` closes:
- L01: `norm_num [Finset.mem_insert, Finset.mem_singleton]` closes membership
- L02: `norm_num` closes the subset goal
- L05: `norm_num` closes `s.card ≤ s.card + s.card` without induction
- L07: `norm_num` closes the concrete cardinality inequality (ignoring `h`)
- L08: `norm_num [Finset.card_union_le]` closes the boss

**Fix**: Add `norm_num` to DisabledTactic for L01, L02, L05, L07, L08. (L03, L04, L06 are not closeable by `norm_num` alone.)

### P1 (high -- should fix)

**P1-1: L03 closeable by library lemma `inf_sup_self`.**

`exact inf_sup_self` closes `s ∩ (s ∪ t) = s` without `ext` or membership reasoning. The learner who knows this mathlib lemma name bypasses the entire ext+membership retrieval.

**Fix**: Add `DisabledTheorem inf_sup_self` to L03. Also add `TheoremDoc inf_sup_self` before it (to avoid build warning).

**P1-2: L05 closeable by `linarith` (even after `simp`, `omega`, `norm_num` are disabled).**

`linarith` closes `s.card ≤ s.card + s.card` without induction.

**Fix**: Add `linarith` to DisabledTactic in L05. But note: even with all automation disabled, the target's insert step does not require `ih` (see P2-2 below). The statement itself is the deeper problem.

**P1-3: L08 boss Part 3 closeable by `exact Finset.card_union_le s t`.**

The library lemma `Finset.card_union_le` exactly matches Part 3's goal `(s ∪ t).card ≤ s.card + t.card`. The intended proof uses `have h := Finset.card_union_add_card_inter s t; omega` (deriving the bound from inclusion-exclusion). Allowing the direct lemma bypasses the inclusion-exclusion + omega reasoning.

**Fix**: Add `DisabledTheorem Finset.card_union_le` to L08. Add `TheoremDoc Finset.card_union_le` before it. The learner must then derive the bound from `card_union_add_card_inter` + `omega`, which is the intended proof.

### P2 (medium -- should fix before shipping)

**P2-1: L04 and L06 closeable by `rfl`.**

Both levels have concrete finset computations that are definitionally true. `rfl` closes:
- L04: `(Finset.filter (fun x => x > 5) ({2, 4, 6, 8, 10} : Finset Nat)).card = 3`
- L06: `(({7, 8, 9} : Finset Nat) ∪ {9, 10, 11}).card + ... = ... + ...`

`rfl` cannot be disabled. This is a known P2 issue with concrete finset cardinality goals (documented in project memory).

**Mitigation**: Accept as P2. The `rfl` exploit requires the learner to know that these computations are definitionally true, which is not obvious. The `rfl` path does teach something (Lean computes these automatically), even if it bypasses the intended proof pattern. No code fix available.

**P2-2: L05 does not exercise the inductive hypothesis.**

Even with all automation disabled, the insert step of `s.card ≤ s.card + s.card` does not require `ih`. After `rw [Finset.card_insert_of_notMem ha]`, the goal is `s'.card + 1 ≤ (s'.card + 1) + (s'.card + 1)`, which is true independently. The enrichment reviewer (R1 and R2) flagged this.

**Fix**: Replace the L05 statement with one where `ih` is genuinely needed. Candidate: `(s.filter p).card ≤ s.card` or `2 * s.card = s.card + s.card` (where `ih` must appear in the insert step). This requires rewriting the level.

**P2-3: Boss is a gauntlet (F8b) -- three independent parts with no interaction.**

The boss statement is `A ∧ B ∧ C` where A, B, C are solved independently. The learner uses `refine ⟨?_, ?_, ?_⟩` and then handles each part in isolation. No planning challenge beyond sequencing. The enrichment reviewer (R1) flagged this as well.

**Fix**: Consider redesigning the boss as a single multi-step goal where the parts interact. For example, prove `(s ∪ t).card ≤ s.card + t.card` by first establishing `s ∩ t ⊆ s` (needed for the bound), then applying inclusion-exclusion, then using the subset-cardinality fact. This would require the learner to see how the pieces fit together.

**P2-4: `sdiff` not warmed up before boss.**

L08 Part 1 uses `Finset.mem_sdiff` but no earlier level in this pset exercises set difference. Every other boss subskill has a warm-up level.

**Fix**: Replace L01 (which is structurally identical to lecture membership levels) with an `sdiff` membership problem: e.g., "Prove `3 ∈ {1, 2, 3, 4} \ {2, 4}`." This warms up `sdiff` and provides a genuinely different surface form.

### P3 (low -- cosmetic)

**P3-1: L08 conclusion references world numbers (W6, W7, etc.) and plan codes (V5, V14, etc.).**

The learner does not see world numbers or plan codes. Use world names and descriptive skill names instead.

**P3-2: L03 conclusion should name the "element-chasing" / "extensionality proof" strategy.**

The enrichment reviewer (R2) flagged this. Adding one sentence naming the pattern would strengthen the transfer value.

---

## 10. What to playtest again after patching

### If P0-1 and P0-2 are fixed (add `simp` + `norm_num` to DisabledTactic):

**Full re-audit required.** Disabling `simp` requires rewriting the model proofs in L01, L02, L04 (inner `have` proof), and L08 (Parts 1). Each rewritten proof must be checked for:
- Interactive quality (can the learner explore incrementally?)
- Hint alignment (do hints match the new proof?)
- Remaining exploits (does `simp only` with auto-discovered lemmas still bypass?)

### If P1-1 is fixed (disable `inf_sup_self` on L03):

Verify L03 compiles with the DisabledTheorem. Check that no other lattice-level lemma closes the goal.

### If P1-3 is fixed (disable `Finset.card_union_le` on L08):

Verify the boss still compiles with the intended proof. Check that no other one-shot lemma closes Part 3.

### If P2-2 is fixed (replace L05 statement):

Full level re-audit of L05: verify the new statement requires `ih`, verify automation is properly gated, verify hints match.

### If P2-3 is fixed (redesign boss):

Full boss re-audit: seeded subskills, closure quality, integration quality, exploit paths.

**Verdict**: The world is NOT shippable in its current state. The `simp` + `norm_num` omission (P0-1, P0-2) must be fixed first. After that, the library lemma exploits (P1-1, P1-3) should be addressed. After P0 and P1 fixes, a full R3 re-audit is needed to verify the fixes and check for any remaining exploits in the rewritten proofs.
