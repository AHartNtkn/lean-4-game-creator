# W12_ps CountingPset -- Playtest Audit (Round 2)

**World**: CountingPset (W12_ps -- Pset, 7 levels)
**Predecessors**: CountingPigeonhole (W12, 10 levels), CountingFunctions (W12_ex, 5 levels)
**R1 verdict**: CONDITIONAL PASS, P1 -- L03 duplicated L02's pigeonhole move instead of testing V15
**R1 fixes applied**: L03 redesigned for subset-card inequality. L04 redesigned for witness extraction. Build passes.

---

## 1. Overall verdict

**CONDITIONAL PASS** -- no P0, one P1, two P2.

The R1 fixes are confirmed: L03 now retrieves V15 (subset-card inequality via `Finset.card_le_card`) and L04 now retrieves V8 (witness extraction from nonemptiness). Both are faithful to the planned retrieval targets and use genuinely different proof shapes from the `rw/omega` template that dominates L01/L02/L05/L06/L07.

The remaining issue is a P1 `norm_num` exploit: bare `norm_num` closes L01 and L06 in one shot, bypassing all `rw` steps. `norm_num` is not disabled on any level in this world. For L02/L05/L07, `norm_num` replaces the `rw [card_fin]; omega` arithmetic steps but the learner still needs `apply Fintype.exists_ne_map_eq_of_card_lt` first, so the key proof move is preserved (P2). For L01 and L06, the bypass is total (P1).

---

## 2. R1 fix verification

### L03 (was: duplicate of L02 pigeonhole; now: subset-card inequality)

**Verified**: L03 now states `s.card <= t.card` given `h : s ⊆ t` on abstract `Finset Nat`. The proof is `exact Finset.card_le_card h`. This is V15 (cardinality monotonicity from subset), first taught in FinsetInduction L06 and previously retrieved in FinsetPset L07. The proof shape (single `exact` with a lemma applied to a hypothesis) is distinct from the `rw/omega` pattern used elsewhere in this world.

**Status**: Fix is correct and effective. V15 retrieval is genuine.

### L04 (was: another rw/omega computation; now: witness extraction)

**Verified**: L04 now states `exists x, x in s` given `h : s.Nonempty`. The intended proof uses `obtain` to destructure `h`, but `exact h` also works since `Finset.Nonempty` is definitionally `exists x, x in s`. The conclusion explains both paths and emphasizes the `obtain` pattern as the pedagogically important one.

This mirrors the original W12 L04 (where V8 was first taught), which had the same statement and the same `exact h` alternative. The pset level is faithfully retrieving V8 on the same definitional relationship. The lesson is about recognizing that nonemptiness provides a witness.

**Status**: Fix is correct. V8 retrieval is genuine. The `exact h` shortcut is inherent to the definitional structure and was already acknowledged in the lecture world.

---

## 3. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Seven distinct retrieval targets now covered: M13/M14 (L01), V16 (L02), V15 (L03), V8/V9 (L04), T5 (L05), T1 (L06), integration (L07). No gaps in planned coverage. |
| 2. Granularity fit | 3 | Each level has a distinct dominant lesson. L03 and L04 now use genuinely different proof shapes from L01/L02. The boss combines product cardinality and pigeonhole. |
| 3. Proof-move teaching | 3 | The world now exercises four distinct proof patterns: rw-then-compute (L01, L06), apply-then-rw-then-close (L02, L05, L07), exact-with-lemma (L03), exact/obtain (L04). The R1 problem of uniform `rw/omega` is resolved. |
| 4. Inventory design | 4 | No new items introduced (correct for a pset). All lemmas are recalled from predecessor worlds. Clean. |
| 5. Hint design and recoverability | 3 | All hints are hidden (appropriate for pset reduced scaffolding). Hints give complete strategy. No layered hints needed since each level is 1-3 steps. |
| 6. Worked example -> practice -> boss | 3 | L01-L04 are retrieval, L05-L06 are transfer, L07 is integration boss. The boss combines product cardinality computation (from L01) with pigeonhole application (from L02). |
| 7. Mathematical authenticity | 3 | Transfer levels (L05, L06) include well-written paper proofs. Boss conclusion has a comprehensive coverage table and transfer moment. |
| 8. Paper-proof transfer | 3 | L05 and L06 provide full paper proofs. L07 conclusion restates the boss proof in mathematical language. |
| 9. Technical fit | 3 | Build passes. Disabled tactic baseline is consistent. TacticDoc info messages are cosmetic (existing docstrings are used). |

**Average**: 3.1 -- passes (>= 3.0 average, no category below 2)

---

## 4. Coverage sanity

### 4a. What is covered

| Item | Axis | L01 | L02 | L03 | L04 | L05 | L06 | L07 |
|------|------|-----|-----|-----|-----|-----|-----|-----|
| `Fintype.card_prod` | MATH | R | | | | | | G |
| `Fintype.card_fin` | MATH | R | R | | | R | R | G |
| `Fintype.card_bool` | MATH | R | | | | | | |
| `Fintype.card_fun` | MATH | | | | | | R | |
| `Fintype.exists_ne_map_eq_of_card_lt` | MATH | | R | | | R | | G |
| `Finset.card_le_card` | MATH | | | R | | | | |
| `Finset.Nonempty` | MATH | | | | R | | | |
| Product cardinality computation | MOVE | R | | | | | | G |
| Pigeonhole collision | MOVE | | R | | | R | | G |
| Subset-card inequality | MOVE | | | R | | | | |
| Witness from nonempty | MOVE | | | | R | | | |
| Exponential formula | MOVE | | | | | | R | |
| Pigeonhole in words | TRANSFER | | | | | T | | |
| Exponential formula in words | TRANSFER | | | | | | T | |
| Product + pigeonhole integration | TRANSFER | | | | | | | T |

### 4b. Coverage gaps

1. **`Fintype.card_option` not retrieved**: Taught in W12 L03, never used in this pset. This was noted in the R1 enrichment review as "Consider" priority (#8). Not a blocking gap since the pset's seven retrieval targets are all covered, but it leaves one taught type constructor unexercised.

2. **V15 (L03) has no integration in the boss**: The boss uses product cardinality + pigeonhole but does not require a subset-card step. The enrichment review noted this as "Consider" priority (#7). Since V15 was already integrated in the FinsetInduction boss (W10 L09) and the FinsetPset boss (W10_ps), this is acceptable. The pset retrieves V15 in isolation (L03), which is sufficient for a pset role.

3. **V8/V9 (L04) has no integration in the boss**: Same pattern as V15. These were integrated in the CountingPigeonhole boss (W12 L10). Isolated retrieval in the pset is sufficient.

---

## 5. Granularity sanity

**Level count**: 7 levels for a pset world covering 7 retrieval targets + 1 integration boss = well-calibrated. No overfine or overbroad levels.

**Proof shape diversity**: After the R1 fix, the world now has four distinct proof patterns:
- `rw [...]; norm_num/rfl` (L01, L06) -- cardinality computation
- `apply ...; rw [...]; omega` (L02, L05, L07) -- pigeonhole application
- `exact Lemma h` (L03) -- direct lemma application
- `exact h` / `obtain` (L04) -- definitional recognition / witness extraction

**Boss seeding**: The boss (L07) requires product cardinality decomposition (seeded by L01) and pigeonhole application (seeded by L02). Both subskills are practiced before the boss.

**Boss integration quality**: The boss combines counting and pigeonhole on a compound type (`Fin 3 x Fin 3 -> Fin 8`). The learner must compute `card (Fin 3 x Fin 3) = 9`, then apply pigeonhole since `9 > 8`. This requires two skills from different levels, which is genuine integration. However, the integration is shallow: the two skills are composed sequentially (`apply` then `rw`), not interleaved. The boss would be stronger if it required reasoning about WHY the product has 9 elements (not just computing it), but for a pset boss this level of integration is acceptable.

---

## 6. Learner simulation

### 6a. Attentive novice

**First likely stuck point**: L01 -- needs to recall `Fintype.card_prod` and `Fintype.card_bool` from W11/W12. The introduction lists these lemmas, and the hidden hint gives the full strategy. Recovery path is adequate.

**Most likely wrong move**: Trying `norm_num` on L01 and discovering it works (P1 exploit). The novice may learn the wrong lesson: "just use norm_num for cardinality."

**Hint rescue**: Hints are hidden (reduced scaffolding). When revealed, they give complete tactic sequences. For a pset, this is appropriate -- the learner should try first, then peek if stuck.

**Lesson legibility**: Each level's intended lesson is stated in the introduction and reinforced in the conclusion. L03 and L04 (the redesigned levels) clearly explain what proof move is being retrieved.

### 6b. Experienced Lean user

**Avoidable friction**: None. Proofs are short (1-4 steps each). No verbose syntax required.

**Alias gaps**: `exact h` on L04 is the natural move for an experienced user. The `obtain` path is pedagogically preferred but not forced. This is acceptable since the level's lesson is about recognizing the definitional equality.

**Inventory clutter**: Zero new items introduced. Clean.

**Needless verbosity**: On L02/L05/L07, the `rw [Fintype.card_fin, Fintype.card_fin]; omega` step can be replaced by `norm_num`. An experienced user would prefer this shorter form, and it works (since `norm_num` is not disabled). This is not hostile -- it's a valid alternative that still requires the key `apply` step.

---

## 7. Pset integrity check

| Check | Verdict |
|-------|---------|
| Fresh surface form | PASS -- all levels use new types/sizes not seen in W12 or W12_ex: `Fin 4 x Bool`, `Fin 7 -> Fin 5`, abstract finsets, `Fin 8 -> Fin 7`, `Fin 4 -> Fin 3`, `Fin 3 x Fin 3 -> Fin 8` |
| Reduced scaffolding | PASS -- all hints are hidden. Introductions give lemma recalls but not step-by-step instructions (except L07 boss which lists what you need) |
| Real retrieval | PASS -- L01-L04 require recalling lemmas/moves from W12 and W10 without step-by-step guidance. L03 and L04 use proof shapes not seen elsewhere in this world |
| Not cloning lecture | PASS -- no level is a number-swapped copy of a W12 or W12_ex level. L03 retrieves V15 (from W10, not W12). L04's nonemptiness context is abstract finsets (vs W12's concrete Fin types) |

---

## 8. Course-role sanity

**Intended role**: Pset -- retrieve counting and pigeonhole skills under reduced scaffolding.

**Actual role**: Matches intent. L01-L04 are genuine retrieval on fresh surface forms. L05-L06 are transfer (Lean proof + paper proof). L07 is integration boss. The world does not introduce new abstract theory (correct for a pset).

**Miscast elements**: None after the R1 fix. L03 and L04 now retrieve the planned skills (V15 and V8/V9 respectively) rather than duplicating L02's pigeonhole move.

---

## 9. Technical risks

### P1: `norm_num` one-shot exploit on L01 and L06

**Verified**: Bare `norm_num` (no arguments) closes both:
- L01: `Fintype.card (Fin 4 x Bool) = 8` -- `norm_num` evaluates the entire expression
- L06: `Fintype.card (Fin 4 -> Fin 3) = 81` -- same

**Impact**: The learner can pass L01 and L06 without using `Fintype.card_prod`, `Fintype.card_fun`, `Fintype.card_fin`, or `Fintype.card_bool`. This bypasses the intended `rw` decomposition lesson.

**Severity**: P1. The learner who uses `norm_num` on L01 still has L03, L04, and L07 where `norm_num` alone doesn't suffice. But two of seven levels become zero-retrieval on the taught proof moves.

**Fix**: Add `norm_num` to `DisabledTactic` on L01 and L06. The intended proofs don't use `norm_num` on L01 (they use implicit `rfl` or `norm_num` is not needed after the rewrites). L06 uses `norm_num` as the final step -- replace with `omega` or verify that post-rewrite goal is closable by `rfl`.

**Note**: `rfl` also closes L01 and L06 directly (verified). Since `rfl` cannot be disabled, this is an accepted P2. The `rfl` exploit is less likely to be discovered by a novice than `norm_num`.

### P2: `norm_num` replaces `rw [card_fin]; omega` on L02, L05, L07

**Verified**: After `apply Fintype.exists_ne_map_eq_of_card_lt`, bare `norm_num` closes the remaining cardinality goal on L02, L05, and L07, replacing the intended 2-step `rw [card_fin, card_fin]; omega`.

**Impact**: The learner still needs the key proof move (`apply` pigeonhole), so the primary lesson is preserved. The bypass only affects the arithmetic verification step.

**Severity**: P2. The `norm_num` shortcut is a valid alternative that an experienced user would prefer. The novice who follows hints will do the `rw + omega` path.

### P2: `rfl` closes L01 and L06

**Verified**: `Fintype.card (Fin 4 x Bool) = 8` and `Fintype.card (Fin 4 -> Fin 3) = 81` are both definitionally true with the `Fintype` instances from Mathlib.

**Impact**: Same as the `norm_num` bypass but harder to discover.

**Severity**: P2 (accepted -- `rfl` cannot be disabled). Documented in project memory as a known pattern for `Fintype.card` on concrete types.

### P2: L04 closable by `exact h` without `obtain`

**Verified**: `s.Nonempty` is definitionally `exists x, x in s`, so `exact h` closes the goal without using `obtain` to extract a witness.

**Impact**: The intended V8 retrieval (using `obtain` to destructure an existential) is not forced. However, the lecture world (W12 L04) had the same `exact h` alternative and considered it pedagogically acceptable. The conclusion explains both paths.

**Severity**: P2 (accepted -- the lesson is about recognizing the definitional equality, which `exact h` demonstrates).

---

## 10. Ranked patch list

| Priority | Level(s) | Issue | Fix |
|----------|----------|-------|-----|
| **P1** | L01, L06 | `norm_num` one-shot exploit bypasses all `rw` steps | Add `norm_num` to `DisabledTactic` on L01 and L06. For L06, replace the intended `norm_num` final step with `omega` or verify `rfl` works post-rewrite |
| **P2** | L02, L05, L07 | `norm_num` replaces `rw [card_fin]; omega` after `apply` | Accept -- key proof move (pigeonhole application) is still required. Optionally add `norm_num` to `DisabledTactic` for consistency |
| **P2** | L01, L06 | `rfl` closes goal directly | Accept -- cannot disable `rfl`. Known Fintype.card pattern |
| **P2** | L04 | `exact h` bypasses `obtain` | Accept -- same design as lecture world W12 L04. Lesson is about definitional recognition |

---

## 11. What to playtest again after patching

1. After disabling `norm_num` on L01 and L06: verify intended proofs still compile. On L06, confirm `omega` or `rfl` closes the post-rewrite goal `3 ^ 4 = 81`. Verify no other one-shot exploit remains on those two levels (test `ring`, `omega`).
2. If `norm_num` is also disabled on L02/L05/L07: verify `omega` still closes the post-rewrite arithmetic goal. (It should -- `omega` handles `5 < 7`, `7 < 8`, `8 < 3 * 3`.)
3. No need to re-audit L03 or L04 -- the R1 fixes are confirmed correct and no new issues found on those levels.
