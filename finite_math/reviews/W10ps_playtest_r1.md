# W10_ps FinsetPset — Playtest Audit R1

**World**: FinsetPset (8 levels)
**Role**: Pset — reduced scaffolding, fresh surface forms, retrieval
**Prerequisite**: FinsetInduction (W10)

---

## 1. Overall Verdict

**NOT PASSING.** Multiple P0 and P1 exploits bypass intended lessons. The boss is vulnerable to library one-liners. L05's statement does not require finset induction at all. `simp` is not disabled and closes multiple levels in one shot. The pset scaffolding reduction is appropriate (all hints are hidden), but the statement designs are not exploit-resistant enough to force genuine retrieval.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good retrieval map across V4-V15, M8-M9, T3-T4. But L05 does not actually retrieve V4. |
| 2. Granularity fit | 3 | Each level targets one skill. No overbroadness. |
| 3. Proof-move teaching | 2 | L05 bypassed by arithmetic. L04 proof is interactive-hostile. Boss parts 2-3 are library lookups. |
| 4. Inventory design | 3 | No new inventory (appropriate for pset). DisabledTactic misses `simp`. |
| 5. Hint design / recoverability | 3 | All hints are hidden (correct for pset). Coverage is adequate. L04 hint is vague ("use `have`") without telling the learner what the filter produces. |
| 6. Worked example -> practice -> transfer -> boss | 2 | Transfer levels (L06, L07) are one-shot `exact` calls. Boss integration is shallow — parts 2-3 close with single library lemmas. |
| 7. Mathematical authenticity | 3 | Good concrete examples. Transfer conclusions in L06/L07 are well written. |
| 8. Paper-proof transfer | 3 | L06 and L07 conclusions do a good job of translating to paper. Boss conclusion covers all three parts. |
| 9. Technical fit / maintainability | 3 | Builds cleanly. Warnings about missing NewTheorem/NewTactic for induction/Nat are pre-existing upstream. |

**Average**: 2.78 — below the 3.0 threshold. Two categories at 2.

---

## 3. Coverage Gaps

| Item | Expected state | Actual state | Issue |
|------|---------------|-------------|-------|
| V4 (Finset.induction_on) | T (transfer) | NOT RETRIEVED | L05 statement is closable by `le_add_self` / `Nat.le_add_right` — no induction needed |
| V6 (ext for finset equality) | T (transfer) | T in L03 | OK, but `inf_sup_self` one-shots it |
| V7 (case analysis on membership) | T (transfer) | T in L03 | OK if L03 exploit is blocked |
| M8 (filter) | T (transfer) | Weak in L04 | `rfl` closes L04 |
| M9 (cardinality) | T (transfer) | Weak in L04 | `rfl` closes L04 |
| `mem_sdiff` | Used in boss | Not taught in any prior world | **Hidden prerequisite** — see defect D3 |

---

## 4. Granularity Defects

- **L05**: The statement `s.card ≤ s.card + s.card` is too trivially true. It does not require induction on the finset structure — it is a fact about natural numbers (`n ≤ n + n`). The "fresh target" needs to be a property that genuinely depends on finset structure, not on arithmetic.

- **L06/L07**: These transfer levels are one-shot `exact` calls. As pset levels, they should require the learner to DO the proof, not just cite a lemma. The transfer value is entirely in the conclusion text, which the learner may not read. Consider requiring the learner to prove the statement from more primitive pieces, or restructuring these as levels where the learner must construct the argument step by step.

---

## 5. Learner Simulation

### Attentive Novice

**L01**: Types `simp` (available!) and it works. Never uses `Finset.mem_insert`. Lesson bypassed.

**L03**: Same novice tries `simp` on the absorption law. It works. Lesson bypassed.

**L04**: The hint says "use `have` to show the filter equals the expected finset." The novice does not know what the filter produces. They need to compute `{6, 8, 10}` mentally. If they try `rfl`, it works immediately. If they follow the hint, they must type a complex `have` with the exact answer before getting any feedback — interactive-hostile.

**L05**: Even with `omega` disabled, the novice who remembers `le_add_self` from NNG4 or who tries `norm_num` bypasses the level entirely. The novice who does use induction succeeds, but the base case and step both close with `omega` — wait, `omega` is disabled here. So the novice who does induction must use `simp` or arithmetic lemmas for the base case `0 ≤ 0 + 0`. This is fine... except `simp` closes the whole thing without induction too. Wait: let me check.

Actually, `simp` closes `s.card ≤ s.card + s.card` directly (confirmed: `le_add_self`). With omega disabled but simp available, simp still closes it.

**L08 Boss**: The novice who knows `Finset.inter_subset_left` and `Finset.card_union_le` closes parts 2 and 3 with one line each. Only Part 1 (sdiff membership) requires multi-step reasoning. This is not a 4+-move integration boss.

**First stuck point**: L04 (computing the filter result is non-obvious; the hint is unhelpful).

**Most likely wrong move**: Trying `simp` everywhere (and it works on L01, L03, L05, and boss Part 1).

### Experienced Lean User

**L01**: `simp` one-shot. No friction because it works, but no learning either.

**L03**: `inf_sup_self` or `simp` one-shot. Knows the library.

**L04**: `rfl`. Knows Lean computes finset operations definitionally.

**L05**: `le_add_self` or `Nat.le_add_right _ _` or `norm_num`. No induction.

**L06**: `exact Finset.card_union_add_card_inter _ _` or `rfl`.

**L07**: `exact Finset.card_le_card h`.

**L08**: `⟨by simp, Finset.inter_subset_left, Finset.card_union_le s t⟩`. No multi-step reasoning at all.

**Avoidable friction**: None — the world is too easy for this persona, not too hard.

**Alias gaps**: None.

---

## 6. Pset Integrity Notes

### Fresh surface form
- L01: Fresh finset `{10, 20, 30, 40}` — YES, fresh surface
- L02: Fresh pair `{5, 10} ⊆ {5, 10, 15, 20}` — YES
- L03: Absorption law (new identity) — YES
- L04: New filter predicate and finset — YES
- L05: New property — YES but the property is trivially true
- L06: New finsets for inclusion-exclusion — YES
- L07: New finsets for subset-cardinality — YES
- L08: New multi-part statement — YES

### Reduced scaffolding
All hints are `hidden := true`. No visible strategy hints. Introduction text provides some guidance but less than lecture worlds. **PASS** on scaffolding reduction.

### Real retrieval
- L01: **FAIL** — `simp` one-shots it, so no retrieval of `mem_insert`
- L02: OK — requires `intro` + case analysis
- L03: **FAIL** — `simp` or `inf_sup_self` one-shots it
- L04: **FAIL** — `rfl` one-shots it
- L05: **FAIL** — `le_add_self` / `norm_num` bypass induction entirely
- L06: OK (the intended proof IS `exact`, but `rfl` also works)
- L07: OK (the intended proof IS `exact`)
- L08: **FAIL** — library lemmas bypass integration

### Problems doing more than cloning lecture
- L06/L07: These ARE lecture clones — same one-shot `exact` pattern with different numbers. The transfer value is in the conclusion text only.

---

## 7. Technical Risks

| Risk | Severity | Details |
|------|----------|---------|
| `simp` not disabled | P0 | `simp` is not in `DisabledTactic` for L01, L02, L03, L04, L06, L07, L08. It one-shots L01, L03, and boss Part 1. |
| `inf_sup_self` not disabled | P1 | `inf_sup_self` (a lattice lemma) closes L03 in one shot without engaging `ext` + membership. |
| `rfl` closes L04 | P2 | The filter + card computation is definitionally true. Cannot disable `rfl`. Accept or redesign statement. |
| `rfl` closes L06 | P2 | The inclusion-exclusion on concrete finsets is definitionally true. Cannot disable `rfl`. |
| L05 statement doesn't need induction | P0 | `s.card ≤ s.card + s.card` is `n ≤ n + n`, closable by `le_add_self`, `norm_num`, or `simp`. No finset structure needed. |
| `Finset.inter_subset_left` closes boss Part 2 | P1 | Library lemma one-shot. Should be disabled or statement redesigned. |
| `Finset.card_union_le` closes boss Part 3 | P1 | Library lemma one-shot. Should be disabled or statement redesigned. |
| `mem_sdiff` is a hidden prerequisite | P1 | Used in boss Part 1 but never introduced in any prior world. The learner must discover it from the hint or introduction text. |
| `norm_num` not disabled on L05 | P1 | `norm_num` closes `s.card ≤ s.card + s.card` even with `omega` disabled. |

---

## 8. Ranked Patch List

### P0 — Blocking

**D1. Add `simp` to `DisabledTactic` on all levels.**
Currently: `trivial decide native_decide aesop simp_all`
Required: `trivial decide native_decide simp aesop simp_all`
`simp` one-shots L01, L03, and boss Part 1. It must be disabled across the pset.

Impact: The intended solutions for L01, L02, L03 use `simp` internally. After disabling `simp`, the solutions must be rewritten to use manual `rw` chains. L01's solution uses `simp [Finset.mem_insert, Finset.mem_singleton]` — replace with explicit `rw` + `left`/`right` chain. L02 uses `simp only [...]` + `rcases ... <;> simp` — replace the final `simp` with manual membership proofs. L03 uses `simp` nowhere in the primary path (good). L04's `have` proof uses `simp only [...]` — replace with explicit `rw` steps. Boss uses `simp [...]` for Parts 1a and 1b — replace with manual membership proofs.

**D2. Redesign L05 to require actual finset induction.**
The statement `s.card ≤ s.card + s.card` is pure arithmetic on `Nat` and does not depend on finset structure at all. Even with `omega` disabled, `le_add_self`, `Nat.le_add_right`, and `norm_num` close it.

Fix: Change the statement to something that genuinely requires induction on the finset structure. For example:
- `∀ (s : Finset α), 0 ≤ s.card` (but this is also trivially `Nat.zero_le`)
- A property like `∀ (f : α → Nat), s.card ≤ (s.image f).card + (s.filter (fun x => (s.filter (fun y => f y = f x)).card ≥ 2)).card` (too complex)
- Better: a statement where the finset structure matters, like proving `s.card = (s.filter p + s.filter (fun x => ¬p x)).card` or similar. Or keep the induction pattern but disable the library shortcuts.

Alternative fix: Add `DisabledTheorem Nat.le_add_right Nat.le_add_left le_add_self le_add_right le_self_add` and disable `norm_num` on this level. Then the only path requires induction. This is the smaller change but risks missing other one-shot lemmas.

Recommended: **Redesign the statement** to depend on finset structure, not just cardinality arithmetic.

### P1 — High

**D3. Disable `Finset.inter_subset_left` in boss (L08).**
This library lemma closes Part 2 (`s ∩ t ⊆ s`) in one shot, bypassing the intended `intro a ha; rw [Finset.mem_inter] at ha; exact ha.1` proof. Add `DisabledTheorem Finset.inter_subset_left` to L08.

**D4. Disable `Finset.card_union_le` in boss (L08).**
This library lemma closes Part 3 in one shot. It was the theorem proved as the FinsetInduction boss — the learner should not be allowed to cite it directly. Add `DisabledTheorem Finset.card_union_le` to L08.

**D5. Disable `inf_sup_self` (and related lattice lemmas) in L03.**
`inf_sup_self` closes the absorption law in one shot. The intended proof uses `ext` + membership reasoning. Add `DisabledTheorem inf_sup_self` (and check for other lattice shortcuts like `Finset.inter_union_self`).

**D6. Address `mem_sdiff` as a hidden prerequisite in boss Part 1.**
`Finset.mem_sdiff` is used in the boss but was never introduced in prior worlds. The introduction text mentions it, but the learner has never practiced it. Either:
- Add a prior level in this pset that practices `mem_sdiff`, or
- Add it as a `NewTheorem` with a `TheoremDoc` entry in the boss level.

**D7. Add `norm_num` to `DisabledTactic` on L05.**
`norm_num` closes the statement without induction. (Also needed after D2 redesign if the new statement is still arithmetic.)

### P2 — Medium

**D8. `rfl` closes L04 and L06.**
The filter+card computation (L04) and the inclusion-exclusion on concrete finsets (L06) are definitionally true. `rfl` cannot be disabled. Accept as a known P2 limitation, or redesign:
- L04: Use a non-decidable predicate, or make the filter depend on a hypothesis, or use abstract finsets.
- L06: Use abstract finsets instead of concrete ones (but then the transfer value of seeing specific numbers is lost).

Recommendation: Accept for L06 (the pedagogical value is in the conclusion text). For L04, consider redesigning with abstract finsets or a variable-dependent filter so `rfl` cannot close it.

**D9. L04 proof is interactive-hostile.**
The intended solution requires a `have` step where the learner must: (1) know the answer (`{6, 8, 10}`) before starting, (2) type a complex `ext x; simp only [...]; omega` subproof. No intermediate feedback until the entire `have` is correct.

Fix: Restructure to use `Finset.filter_insert` rewrites that peel off one element at a time, giving feedback after each step. Or provide a more structured hint that guides the learner through intermediate steps.

**D10. L06/L07 are effectively lecture clones.**
Both levels use the same one-shot `exact` pattern as their lecture counterparts (W9 L07 and W10 L06). The only difference is the specific numbers. For a pset, the proof should require more than citing a lemma.

Fix: Restructure so the learner must build the argument from more primitive pieces (e.g., prove inclusion-exclusion for this specific case by computing each side manually, then comparing). Or combine them into a single level where the learner must use both principles in sequence.

---

## 9. What to Playtest Again After Patching

1. **L01, L02, L03 after `simp` is disabled** — verify the manual solutions still compile and are interactive-friendly.
2. **L05 after statement redesign** — verify the new statement genuinely requires finset induction and cannot be bypassed.
3. **L08 boss after `DisabledTheorem` additions** — verify the boss still compiles with the intended solution and that no other library shortcuts exist.
4. **L03 after `inf_sup_self` is disabled** — verify no other lattice lemmas close it.
5. **L04 if redesigned** — verify the new version resists `rfl` and has an interactive-friendly proof path.
6. **Re-check all levels for `norm_num` exploits** after `simp` is disabled (since `norm_num` may become the next easiest bypass).
