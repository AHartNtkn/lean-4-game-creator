# W17 Factorials — Playtest Audit R1

**World**: Factorials (W17)
**Type**: Lecture, 7 levels
**Auditor**: Playtest auditor (R1)
**Build**: Passes (8311 jobs, no errors)

---

## 1. Overall Verdict

**NEEDS REVISION.** The world has solid pedagogical structure and good narrative, but serious exploitability defects undermine nearly every level. Three levels are closable by `rfl` (definitional equality), `norm_num` closes five of seven levels, and two levels have direct one-shot library lemmas that bypass the intended proof entirely. The boss is closable by both `norm_num` alone and by `exact Nat.factorial_eq_prod_range_add_one n`. These must be addressed before the world can be considered clean.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good factorial/descFactorial coverage, but descFactorial_self identity is taught without noting the library lemma |
| 2. Granularity fit | 3 | Each level has a clear dominant lesson; world is coherent |
| 3. Proof-move teaching | 3 | Recursive unfolding + induction are well taught |
| 4. Inventory design | 2 | Missing DisabledTheorem for exploitable lemmas; norm_num not disabled |
| 5. Hint design | 3 | Layered hints at each step; rescue paths present |
| 6. Progression | 3 | Worked example -> practice -> induction -> boss |
| 7. Mathematical authenticity | 3 | Good transfer moments, concrete examples |
| 8. Paper-proof transfer | 4 | L05 and L07 conclusions explicitly map Lean to paper proof |
| 9. Technical fit | 2 | Exploit vulnerabilities are systemic |

**Average: 2.9** (below the 3.0 threshold for "good")

---

## 3. Coverage Gaps

### 3a. Coverage items delivered

| Item | Axis | States | Notes |
|------|------|--------|-------|
| Nat.factorial | MATH | I(L01), S(L02,L03), G(L07) | Good closure |
| Nat.factorial_succ / factorial_zero | LEAN | I(L01), S(L02,L03,L06), G(L07) | Good closure |
| Nat.descFactorial | MATH | I(L04), S(L05) | Not integrated into boss |
| descFactorial_succ / _zero | LEAN | I(L04), S(L05) | Adequate |
| succ_descFactorial_succ | LEAN | I(L05) | Only used once |
| Finset.prod_range_succ | LEAN | S(L03), G(L07) | Retrieval from W15 |
| mul_comm | LEAN | S(L02), G(L07) | Basic algebra retrieval |
| induction | MOVE | S(L05), G(L07) | Retrieval from earlier |
| Fintype.card_perm | LEAN | I(L06) | Only used once |
| Recursive unfolding | MOVE | I(L01), S(L03,L04), G(L07) | Good closure |

### 3b. Gaps

- **descFactorial not integrated into boss**: descFactorial (L04-L05) is introduced and practiced but never appears in the boss or in integration with factorial. It sits as a side thread. The plan says M27(G) for L07 but descFactorial is part of M27. This is a coverage gap — the learner could skip L04-L05 entirely and still complete L06-L07.
- **succ_descFactorial_succ has no supported practice**: Introduced in L05 and used exactly once. Learner has no chance to practice it before it's needed.
- **Fintype.card_perm has no retrieval**: Introduced in L06 and never revisited. This is acceptable for a preview but should be noted.

---

## 4. Granularity Defects

### 4a. Overfine levels

- **L01 and L04 are structurally identical**: Both are "compute a concrete value by unfolding recursion." L01 unfolds factorial, L04 unfolds descFactorial. The proof shape is the same: repeat `rw [succ_lemma]`, then `rw [zero_lemma]`. The second instance teaches no new proof move — only a new definition. This is acceptable for a lecture world (L04 introduces descFactorial), but the repetition should be acknowledged.

### 4b. Potential overbreadth

- **L03 has two unfolding burdens**: The learner must unfold both the product (4 applications of `prod_range_succ` + `prod_range_zero`) AND the factorial (4 applications of `factorial_succ` + `factorial_zero`), then close with `ring`. That is three distinct phases in one level. The hidden hint gives the full chain, which helps, but a novice who doesn't use hidden hints will struggle with the two-sided unfolding. **P2.**

---

## 5. Statement Exploitability (Ranked)

### P0 — Blocking

**[E1] L07 Boss: `norm_num` closes the goal in one tactic.**
```
example (n : ℕ) : Nat.factorial n = ∏ i ∈ Finset.range n, (i + 1) := by norm_num
```
This completely bypasses induction, recursive unfolding, and mul_comm — every skill the boss is supposed to integrate. The boss teaches nothing if `norm_num` is available.

**Fix**: Add `norm_num` to DisabledTactic for L07 (and likely all levels in this world).

**[E2] L07 Boss: `exact Nat.factorial_eq_prod_range_add_one n` closes it in one shot.**
The conclusion of L03 explicitly names this lemma. A learner who reads L03's conclusion and copies the name bypasses the boss entirely.

**Fix**: Add `DisabledTheorem Nat.factorial_eq_prod_range_add_one` to L07.

**[E3] L05: `exact Nat.descFactorial_self n` closes the goal.**
The library lemma `Nat.descFactorial_self` is the exact statement being proved. The intended proof by induction is completely bypassed.

**Fix**: Add `DisabledTheorem Nat.descFactorial_self` to L05.

### P1 — High

**[E4] L01: `rfl` closes `Nat.factorial 5 = 120`.**
Both sides reduce to the same normal form. `rfl` is a core tactic that cannot be disabled, so this is a structural issue with the statement. `norm_num` also closes it.

**Fix**: Cannot disable `rfl`. Add `norm_num` to DisabledTactic. Accept `rfl` as P2 (known limitation for definitional equalities on concrete Nat computations — see MEMORY.md).

**[E5] L03: `rfl` closes `∏ i ∈ Finset.range 4, (i + 1) = Nat.factorial 4`.**
Same as E4 — definitional equality.

**Fix**: Same as E4. Add `norm_num` to DisabledTactic. Accept `rfl` as P2.

**[E6] L04: `rfl` closes `Nat.descFactorial 5 3 = 60`.**
Same pattern.

**Fix**: Same as E4/E5.

**[E7] L06: `norm_num [Fintype.card_perm, Fintype.card_fin]` closes the goal in one tactic.**
While `norm_num` alone doesn't work, passing the two key lemmas as simp-lemma arguments makes it one-shot.

**Fix**: Add `norm_num` to DisabledTactic for L06.

### P2 — Medium (accepted limitations)

**[E8] L01, L03, L04: `rfl` closes these levels.**
Cannot disable `rfl`. This is a known limitation for concrete Nat computations. The learner who discovers `rfl` still learns something (definitional reduction), but misses the recursive unfolding lesson. Acceptable because the game doesn't teach `rfl` as a strategy for these patterns — a learner who tries `rfl` is already somewhat experienced.

---

## 6. Learner Simulation

### 6a. Attentive Novice

**L01**: Clear entry point. The intro explains the recursion well. The novice will follow hints and apply `rw [Nat.factorial_succ]` five times. The repetition is pedagogically effective — the learner builds muscle memory for recursive unfolding.

**L02**: The novice may struggle with the idea of "rewriting the right-hand side." The hint says to use `rw [Nat.factorial_succ]`, which rewrites wherever it matches. The novice may not understand which side changes. After the rewrite, `mul_comm` is straightforward. **First likely stuck point**: understanding that `rw [Nat.factorial_succ]` rewrites the `Nat.factorial (n + 1)` on the RHS.

**L03**: The novice faces a two-phase unfolding. The first hint says "use prod_range_succ," which is fine. But after 4+1 rewrites on the left, the novice must then do 4+1 rewrites on the right. The hidden hint gives the full chain, but the intermediate state after the product unfolding may be confusing — the goal will be a large numeric expression on the left and `Nat.factorial 4` on the right. **Most likely wrong move**: trying `ring` too early (before unfolding the factorial side).

**L04**: Straightforward — same pattern as L01. The intro's worked example of the recursion is helpful.

**L05**: This is the first induction in the world. The novice needs to remember `induction n with` syntax from earlier worlds. The proof shape is well-scaffolded: each case has clear hints. **Most likely wrong move in base case**: trying `rfl` instead of the two rewrites (which would actually work, but misses the lesson).

**L06**: The novice encounters `Equiv.Perm` and `Fintype.card` for the first time. The intro explains these clearly. The proof is mechanical: `rw [card_perm]`, `rw [card_fin]`, then unfold factorial. **First stuck point**: the learner may not have `Fintype.card_fin` in their mental inventory — it's assumed from earlier but not re-introduced here.

**L07**: The boss induction is well-scaffolded with hints at every step. A novice who completed L05 will recognize the pattern. **Stuck point**: the `mul_comm` step at the end requires seeing that the two sides differ only in multiplication order. The hint explains this clearly.

### 6b. Experienced Lean User

**L01, L03, L04**: Will immediately try `rfl` or `norm_num` and succeed. Bypasses the lesson entirely. This is the critical problem.

**L02**: Will do `rw [Nat.factorial_succ, mul_comm]` in one line. Acceptable — this is a natural two-step proof.

**L05**: Will try `exact Nat.descFactorial_self n` and succeed. Bypasses induction entirely. Alternatively, `exact?` will find it. **This is E3.**

**L06**: Will try `decide` or `norm_num [Fintype.card_perm, Fintype.card_fin]`. `decide` is disabled. `norm_num` with hints works. **This is E7.**

**L07**: Will try `exact Nat.factorial_eq_prod_range_add_one n` and succeed. The lemma is named in L03's conclusion. Alternatively, `norm_num` alone closes it. **These are E1 and E2.**

**Avoidable friction**: None significant. The proof steps are clean and well-decomposed.

**Alias gaps**: None — the world uses standard mathlib names.

---

## 7. Boss Integrity (L07)

### Seeded subskills
- [x] Induction (L05, and earlier worlds)
- [x] `Nat.factorial_succ` (L01, L02)
- [x] `Finset.prod_range_succ` (L03, and W15)
- [x] `mul_comm` (L02, and earlier worlds)
- [x] `Nat.factorial_zero` (L01)
- [x] `Finset.prod_range_zero` (L03)

### Closure quality
Good. Every tactic step in the boss proof has been practiced in at least one earlier level. The induction + recursive unfolding pattern was practiced in L05.

### Integration quality
**Moderate.** The boss combines induction with factorial unfolding and product unfolding, plus `mul_comm`. However, the structure is quite close to L05: induction, rewrite both sides, close by algebraic identity. The boss adds `prod_range_succ` to the mix, which is new in combination with induction, but the overall proof shape is the same as L05. The boss is **not** a gauntlet (the parts interact via the inductive hypothesis), but the integration challenge is modest.

### Surprise burden
Low. The boss proof follows the same induction + rewrite pattern as L05. The new element is using `prod_range_succ` in the inductive step, which was practiced in L03.

### Can the learner explain why the proof works?
Yes — the conclusion's transfer moment explicitly maps the proof to a paper proof. The learner should be able to say: "We prove by induction that n! equals the product of 1 through n. The base case is trivial. In the inductive step, we unfold (n+1)! into (n+1)*n!, apply the IH to replace n! with the product, and then peel (n+1) off the product to match."

### Exploitability (CRITICAL)
The boss is closable by `norm_num` and by `exact Nat.factorial_eq_prod_range_add_one n`. Both must be disabled. **P0.**

---

## 8. Course-Role Sanity

The world is correctly cast as a **Lecture** world. It introduces factorial and descending factorial, provides worked examples and practice, and culminates in an integration boss. The progression is:

- L01: First contact (factorial definition + computation)
- L02: Supported practice (factorial recursion as algebra)
- L03: Connection/transfer (factorial as big product — concrete)
- L04: First contact (descending factorial)
- L05: Integration (descFactorial_self by induction)
- L06: Preview/application (counting permutations)
- L07: Boss (general identity by induction)

This is a sound sequence. However, L04-L05 (descending factorials) are somewhat isolated from L06-L07. The learner could skip L04-L05 and still complete the boss. This is not necessarily wrong for a lecture world (the world teaches multiple related topics), but it means descFactorial coverage has no integration checkpoint.

---

## 9. Technical Risks

1. **`norm_num` not disabled on any level.** This is the single biggest technical risk. `norm_num` closes L01, L03, L04, L06 (with hints), and L07 outright. It must be added to DisabledTactic.

2. **No `DisabledTheorem` anywhere.** Two library lemmas (`Nat.descFactorial_self`, `Nat.factorial_eq_prod_range_add_one`) are exact matches for L05 and L07 statements. Both must be disabled.

3. **`rfl` closes L01, L03, L04.** Cannot be disabled. Accepted as P2 per project convention.

4. **L03 conclusion names the L07 boss lemma.** The text explicitly says "In Lean, this is `Nat.factorial_eq_prod_range_add_one`" and gives the full signature. A learner reading L03 can copy this name into L07. Even after disabling the theorem, the conclusion text should be revised to avoid naming the exact lemma the boss proves.

5. **`Fintype.card_fin` is used in L06 but not introduced.** It's likely introduced in an earlier world (FintypeClass or similar), but the level doesn't declare `NewTheorem` for it — it's assumed known. This is fine if it was indeed taught earlier but should be verified.

---

## 10. Ranked Patch List

| Priority | ID | Level | Fix |
|----------|----|-------|-----|
| P0 | E1 | L07 | Add `norm_num` to DisabledTactic |
| P0 | E2 | L07 | Add `DisabledTheorem Nat.factorial_eq_prod_range_add_one` |
| P0 | E3 | L05 | Add `DisabledTheorem Nat.descFactorial_self` |
| P0 | E1+ | ALL | Add `norm_num` to DisabledTactic on ALL 7 levels (systemic) |
| P1 | E7 | L06 | `norm_num` already covered by E1+; verify it's sufficient |
| P1 | T1 | L03 | Revise conclusion to NOT name `Nat.factorial_eq_prod_range_add_one` — instead say "Mathlib has a general version of this identity" without giving the exact name |
| P2 | E4-6 | L01,L03,L04 | Accept `rfl` exploit (cannot disable); document in reviews |
| P2 | C1 | L05 | `succ_descFactorial_succ` introduced and used only once — no supported practice. Consider adding a practice level or accept for lecture world |
| P2 | G1 | L03 | Two-sided unfolding is borderline overbroad. Consider adding a visible (not hidden) intermediate hint after the product unfolding saying "now unfold the factorial side" |

---

## 11. What to Playtest Again After Patching

1. **L07 after disabling `norm_num` and `Nat.factorial_eq_prod_range_add_one`**: Verify the intended proof still works and no other one-shot exploits exist.
2. **L05 after disabling `Nat.descFactorial_self`**: Verify the intended induction proof still works.
3. **All levels after adding `norm_num` to DisabledTactic**: Verify that `ring` (used in L03) is not affected by `norm_num` disabling. `ring` should remain available.
4. **L03 after conclusion text revision**: Verify the new text is accurate and doesn't name any exploitable lemma.
5. **Re-run full exploit scan**: After patches, check for any remaining one-shot tactics (especially `exact?` results on patched levels).
