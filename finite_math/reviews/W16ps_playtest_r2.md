# W16_ps BigOpPset -- Playtest Audit R2

## 1. Overall Verdict

**CONDITIONAL PASS -- 2 issues remain (1 P1, 1 P2)**

The R1 blocking issue (boss repeated W14 identity) has been fixed. The boss now uses the fresh identity `sum (2i+3) = n*(n+2)`, which does not duplicate any prior boss statement. The build passes cleanly. DisabledTactic is applied consistently across all 8 levels. The world structure (7 retrieval levels + 1 boss) is appropriate for a pset.

However, two issues remain:

1. **P1: Boss summand `2*i + 3` recycled from W15 L05** -- The pset boss uses the same summand expression as the W15 `sum_add_distrib` introduction level. For a pset that is supposed to exercise skills on "fresh surface forms," this is a surface-form recycling defect. The identity itself (`= n*(n+2)`) is fresh, but the summand is not.

2. **P2: L01 is an exact statement duplicate of W14 L05 and L07** -- BigOpPset L01 proves `sum i in range n, 2 = 2 * n`, which is literally the same statement as RangeSumInduction L05 and L07. A pset level should use a genuinely fresh surface form, not replay a lecture exercise.

These are not blocking but should be fixed before the world is considered clean.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Retrieves V3, V11, V20, M25, M26, M38, T2, T10. No new items introduced (correct for pset). Missing: V12 (reindexing) and L12 (conv) are not retrieved despite being W16 signature skills. |
| 2. Granularity fit | 3 | Each level isolates one retrieval task. L04/L05 are one-step levels (acceptable for pset). L06 is rfl-only (transfer happens in conclusion). |
| 3. Proof-move teaching | 3 | Pset correctly does not introduce new proof moves. Retrieval is genuine for induction, peel, ring, filter, double-sum interchange. |
| 4. Inventory design | 4 | No new items introduced -- correct for a pset. No clutter. |
| 5. Hint design | 3 | All hints are hidden (reduced scaffolding, appropriate for pset). Every level has at least one rescue hint. Boss has step-by-step hidden hints. |
| 6. Progression | 3 | Moves from single-technique retrieval (L01-L05) to transfer (L06-L07) to integration (L08). This is a sound pset arc. |
| 7. Mathematical authenticity | 3 | Boss identity is genuine. Transfer levels (L06-L07) connect Lean to paper well. LaTeX in intros is correct. |
| 8. Paper-proof transfer | 4 | L06 (read sigma notation) and L07 (write paper proof) are dedicated transfer levels. Boss conclusion includes full paper proof. Strong. |
| 9. Technical fit | 4 | Build clean. DisabledTactic consistent (`trivial decide native_decide simp aesop simp_all`) on all 8 levels. No build warnings beyond pre-existing TacticDoc info messages. |

**Average: 3.3 -- passes the 3.0 threshold. No category below 2.**

---

## 3. Coverage Gaps

### P2: W16 signature skills not retrieved

The pset covers W13-W16 material but notably omits retrieval of:

- **`conv` (L12)** -- The signature new tactic of W16. No pset level exercises `conv`. The W16 boss used `conv` heavily. A pset that covers "big-operator fluency" for W13-W16 should include at least one `conv` retrieval.
- **Reindexing (V12)** -- W16 L07-L08 taught reindexing via `sum_nbij'` and `sum_equiv`. No pset level retrieves this.

The plan's L3 specification says "Retrieval of V20, L7" and mentions `congr`, but the actual L03 does not use `congr` -- it uses `sum_add_distrib` + `mul_sum`. This means L11 (`congr` tactic) is also not retrieved.

These omissions are acceptable at P2 because:
- The pset has 8 levels and cannot cover everything.
- The plan explicitly lists what each level retrieves and does not specify `conv` or reindexing for any pset level.
- `conv` and reindexing are complex enough to warrant their own dedicated practice, which could come in later psets or review worlds.

However, if the enrichment reviewer flagged this, adding a `conv`-based retrieval level would be a clear improvement.

---

## 4. Granularity Defects

### P2: L01 is a statement duplicate

BigOpPset L01 proves exactly `sum i in range n, 2 = 2 * n`. This is the same statement as:
- RangeSumInduction L05 ("A slightly harder sum")
- RangeSumInduction L07 ("Inductive step in detail")

A pset level must use a fresh surface form. The learner literally already proved this exact statement twice. The retrieval is not genuine -- it is replay.

**Fix**: Change the constant to something not used elsewhere (e.g., `sum 7 = 7 * n`, or `sum 4 = 4 * n`), or use a different summand entirely (e.g., `sum (i + 1) = n + sum i`).

### L04 and L05 are true one-step levels

L04 (`rw [Finset.sum_filter]`) and L05 (`exact Finset.sum_comm`) are single-step proofs. This is fine for a pset -- the point is retrieval, and the reduced scaffolding (only hidden hints) means the learner must recall the lemma name independently. Not a defect.

### L06 is trivially `rfl`

L06 is a deliberate transfer level where the Lean proof is `rfl` and the real work is in the conclusion's translation table. This is a sound design pattern for transfer levels. Not a defect.

---

## 5. Learner Simulation

### Attentive Novice

**First likely stuck point**: L01 or L02. The novice needs to recall the induction+peel+ring pattern from W14/W15 without scaffolding. The hidden hint provides the structure, but the novice must actively choose `induction n with` as the opening move.

**Most likely wrong move**: On L03, trying `ring` on the whole goal (it won't work because the goal involves sums). The novice may not remember that `sum_add_distrib` is needed first. The hidden hint rescues well: "Split the sum using `rw [Finset.sum_add_distrib]`, then pull the constant out with `rw [<- Finset.mul_sum]`."

**Hint rescue quality**: Adequate. All hints are hidden (appropriate for a pset). Each level has at least one hint that gives the complete proof strategy. The boss has hints at every step.

**Legibility of lessons**: The retrieval-check labels in conclusions ("You retrieved V3", "You retrieved M38") are helpful for self-assessment. The transfer table in L08's conclusion is excellent.

**L06/L07 experience**: L06 may confuse a novice who expects a real proof. The introduction says "the Lean proof is trivial" and "the real lesson is in the conclusion," which is honest. L07's paper proof in the conclusion is a genuine teaching moment.

### Experienced Lean User

**Avoidable friction**: None identified. The one-step levels (L04, L05) are clean for an expert. The expert can breeze through all levels in under 5 minutes.

**Specific exploits**:

| Level | Exploit | Severity | Notes |
|-------|---------|----------|-------|
| L01 | `omega` (if it works on sum goals) | P3 | Unlikely to close sum goals; would need testing |
| L03 | `congr 1; ext; ring` (then `rw [<- Finset.mul_sum]`) | P3 | Alternative path, still requires knowledge |
| L08 | No exploit -- induction is forced | -- | Good |

No P0 or P1 exploits found. The disabled tactic set (`trivial decide native_decide simp aesop simp_all`) blocks the main automation paths. `omega` and `norm_num` are available but cannot close sum/product goals without induction.

**Alias gaps**: None. The pset uses only previously-taught API.

**Inventory clutter**: None. No new items introduced.

---

## 6. Pset Integrity Notes

### Fresh surface form check

| Level | Claimed retrieval | Surface form | Fresh? |
|-------|------------------|-------------|--------|
| L01 | V3, V11 (induction + peel) | `sum 2 = 2 * n` | **NO** -- exact duplicate of W14 L05/L07 |
| L02 | M25 (multiplicative induction) | `prod 3 = 3^n` | Borderline -- W15 L04 uses `prod 2 = 2^n`, this changes only the constant |
| L03 | V20, L7 (algebraic manipulation) | `sum (5i + i^2) = 5*sum(i) + sum(i^2)` | Borderline -- W15 boss uses `sum (3i + i*i)`, same structure with different constant |
| L04 | M38 (sum_filter) | filter with `< 5` predicate | **YES** -- W16 used `Even` predicate, this is genuinely different |
| L05 | M26 (sum_comm) | double sum of `f i * g j` | **YES** -- W16 used `f i j`, this uses a product structure |
| L06 | T10 (read sigma notation) | `sum (i^2 + 1)` | **YES** -- transfer level, form is new |
| L07 | T2 (write paper proof) | `sum 5 = 5n` | Adequate -- the Lean proof uses a known identity but the paper translation is the novel task |
| L08 | V3, V20, M25 (boss integration) | `sum (2i + 3) = n*(n+2)` | **MIXED** -- identity is fresh but summand `2i+3` appears in W15 L05 |

**Assessment**: L04, L05, L06 are genuinely fresh. L02, L03 are borderline (constant changes only). L01 is a duplicate. L08's summand is recycled. Overall, 3 of 8 levels have surface-form freshness issues.

### Reduced scaffolding check

All hints are hidden (`hidden := true`). No visible strategy hints appear. This is correct for a pset -- the learner must attempt the problem before getting help. **PASS**.

### Real retrieval check

Every level requires the learner to recall a technique from a prior world without being told which technique to use (beyond the level title). The introduction text describes the mathematical goal but does not name specific lemmas (except L03 which names `sum_add_distrib` and `mul_sum`). L03's introduction partially violates the "reduced scaffolding" principle by naming the exact lemmas needed. This is P3 (minor).

---

## 7. Technical Risks

1. **Build clean**: Yes. Only `info`-level warnings about TacticDoc for disabled tactics, which are defined in earlier worlds and would resolve in a full game build.

2. **DisabledTactic consistency**: All 8 levels use the same set: `trivial decide native_decide simp aesop simp_all`. This is the standard baseline set. **PASS**.

3. **No DisabledTheorem**: No `DisabledTheorem` declarations appear. For this pset, no exploitable library lemmas were identified that would close any level in an unintended way. **PASS**.

4. **`omega` availability**: `omega` is not disabled and is available on all levels. It cannot close any of the sum/product goals because they involve `Finset.sum`/`Finset.prod` which `omega` does not understand. **No risk**.

5. **`norm_num` availability**: `norm_num` is not disabled. It cannot close any of these goals either (they are universally quantified over `n` with sum/product operators). **No risk**.

6. **`ring` availability**: `ring` is available and is part of the intended proof path for L01, L02, L07, L08. It cannot close goals that involve `Finset.sum` without prior rewrites. **No risk**.

---

## 8. Ranked Patch List

### P1 (High)

1. **Change the boss summand to avoid recycling from W15 L05.** The summand `2*i + 3` appeared in W15's `sum_add_distrib` introduction. Change to a genuinely fresh expression. Examples:
   - `sum (3*i + 5) = n*(3*n + 7)/2` (but this involves division, may need different formulation)
   - `sum (4*i + 1) = n*(2*n - 1)` -- wait, `4*0 + 1 + 4*1 + 1 + ... = 2n^2 + n - n = 2n^2`... let me compute: `sum_{i=0}^{n-1} (4i+1) = 4*n*(n-1)/2 + n = 2n^2 - 2n + n = 2n^2 - n = n*(2n-1)`. This works.
   - `sum (2*i + 5) = n*(n + 4)`. Compute: `sum = 2*n*(n-1)/2 + 5n = n^2 - n + 5n = n^2 + 4n = n*(n+4)`. This works and keeps the linear form.
   - Simplest fix: change `3` to `5` to get `sum (2*i + 5) = n*(n+4)`.

### P2 (Medium)

2. **Change L01's statement to a genuinely fresh constant sum.** Replace `sum 2 = 2*n` (which duplicates W14 L05/L07) with a different constant like `sum 7 = 7*n` or `sum 4 = 4*n`.

3. **Consider removing lemma names from L03's introduction.** The intro says "use `sum_add_distrib`" and "`<- mul_sum`" by name, which reduces the retrieval demand. For a pset, the intro should describe the mathematical goal and let the learner recall the lemma names from their inventory. Example: "This requires splitting the sum of a combined expression and factoring out a constant."

### P3 (Low)

4. **L02 uses `prod 3 = 3^n` which is very similar to W15 L04's `prod 2 = 2^n`.** The constant change (2 to 3) is minimal surface variation. Consider using a different base like 5 or a different product structure. This is P3 because the multiplicative setting is less familiar than the additive one, so even a small constant change provides some retrieval value.

5. **L03 uses `sum (5i + i^2)` which closely mirrors the W15 boss `sum (3i + i*i)`.** The constant change (3 to 5) and notation change (i*i to i^2) provide some freshness, but the proof structure is identical (minus the `sum_congr` step). This is P3 because the W15 boss also needed `sum_congr` while L03 does not, making L03 genuinely simpler.

---

## 9. What to Playtest Again After Patching

If P1 and P2 are fixed:

1. **The new boss statement** -- verify build, verify the proof pattern still works (induction + peel + ring), verify the identity is mathematically correct.
2. **The new L01 statement** -- same checks.
3. **Full world build** -- `lake build Game.Levels.BigOpPset`.

If L03's intro text is also changed (P2 #3):
4. **L03 intro** -- verify hints still match the level and that the mathematical description is clear enough without naming specific lemmas.

---

## 10. R1 Issue Resolution

**R1 P1: Boss repeated W14 identity** -- **RESOLVED.** The boss now uses `sum (2*i + 3) = n*(n+2)`, which is distinct from:
- W14 boss: `sum (4*i + 3) = n*(2*n + 1)`
- W14 L06: `sum (2*i + 1) = n^2`
- W14 L03/L05/L07: `sum 1 = n`, `sum 2 = 2*n`

The identity itself is fresh. The remaining issue is that the summand `2*i + 3` appeared in W15 L05 (a different world and a different purpose, but still surface recycling in a pset context).

---

## Summary

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| R1-1 | Boss repeated W14 identity | P1 | **FIXED** |
| R2-1 | Boss summand `2i+3` recycled from W15 L05 | P1 | NEW |
| R2-2 | L01 exact duplicate of W14 L05/L07 | P2 | NEW |
| R2-3 | L03 intro names lemmas (reduces retrieval) | P2 | NEW |
| R2-4 | L02 minimal constant variation from W15 L04 | P3 | NEW |
| R2-5 | L03 minimal constant variation from W15 boss | P3 | NEW |
