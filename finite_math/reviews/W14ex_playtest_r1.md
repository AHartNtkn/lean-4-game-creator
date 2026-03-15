# W14_ex SumFormula — Playtest Audit R1

## 1. Overall Verdict

**Needs revision.** The world compiles and follows a logical narrative arc (concrete checks, decomposed proof, assembly, transfer), but has several issues: L01/L02 are near-duplicates with minimal pedagogical differentiation, L06 is not a genuine transfer level (same Lean statement as L05), `Finset.sum_range_zero` is used in hints but never introduced via `NewTheorem`, and the world does not introduce `induction` despite requiring it. The coverage closure for the world's key move (inductive sum proof) is reasonable but the transfer level is hollow.

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 2 | `sum_range_zero` used but not introduced. `induction` required but not introduced. Transfer level is cosmetic. |
| Granularity fit | 2 | L01/L02 are near-duplicates (both just `norm_num`). L06 duplicates L05's statement. |
| Proof-move teaching | 3 | The inductive-sum template (peel, distribute, apply IH, algebra) is well-taught across L03-L05. |
| Inventory design | 2 | `Nat.mul_add` properly introduced. But `sum_range_zero` and `induction` missing from inventory. |
| Hint design / recoverability | 3 | Hints are layered (strategy + hidden code). L04 is particularly well-hinted step by step. |
| Worked example -> practice -> transfer -> boss | 2 | No real boss. L06 "transfer" is just L05 again with a paper proof in the intro text. |
| Mathematical authenticity | 3 | Good historical framing (Gauss). Clear connection to the formula. Avoids subtraction pitfall (explained). |
| Paper-proof transfer | 2 | The Lean-to-paper correspondence table in L06 is excellent exposition, but the level itself doesn't force the learner to engage with it. |
| Technical fit / maintainability | 3 | Compiles cleanly. Dependencies correct. Minor build warnings about missing inventory introductions. |

**Average: 2.4 — below the 3.0 threshold.**

## 3. Coverage Gaps

### P0: `Finset.sum_range_zero` never introduced
- Used in L01 and L02 inside `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`
- The learner is told to use this lemma in hints but it's not in their inventory
- Build warns: "No world introducing Finset.sum_range_zero, but required by SumFormula"
- Fix: Add `NewTheorem Finset.sum_range_zero` (with `TheoremDoc`) in L01

### P1: `induction` tactic never introduced
- Build warns: "No world introducing induction, but required by SumFormula"
- `induction` was introduced in the predecessor world RangeSumInduction (L03 uses it), but there's no `NewTactic induction` declaration there either
- This is a systemic issue across the course, not specific to this world, but should be flagged
- Fix: Ensure `NewTactic induction` appears in an earlier world (e.g., FinsetInduction or RangeSumInduction)

### P2: Transfer level (L06) doesn't force transfer
- L06 has identical statement and proof to L05
- The paper proof correspondence table is in the introduction text, which is passive reading
- The learner just re-solves L05 from memory (or copies their approach)
- True transfer would require the learner to engage with the paper proof form — but lean4game can't assess written text
- This is a fundamental limitation, so the world should acknowledge it honestly rather than pretending L06 is transfer
- Fix: Either (a) change L06 to a slightly different sum formula (e.g., sum of first n odd numbers = n^2) so the learner transfers the *method* to a new problem, or (b) restructure the conclusion to explicitly say "the transfer is cognitive — apply this template to other sum identities"

## 4. Granularity Defects

### P1: L01 and L02 are near-duplicates
- Both use the exact same proof: `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`
- L01 checks n=4, L02 checks n=2
- L02's introduction advertises a "manual unfolding" path, but the canonical proof is still the same `norm_num` one-liner
- The learner gains nothing from L02 that L01 didn't already teach
- Fix: Either (a) merge into one level with a clearer manual-unfolding emphasis, (b) make L02 require the manual path by disabling `norm_num` on it, or (c) replace L02 with a different pedagogical step (e.g., have the learner verify the formula for n=0 specifically to preview the base case)

### P2: L03 (base case) is trivially closed by `rfl`
- The entire level is `rfl` — one character
- This is fine if the level exists to isolate the concept of "base case", but the level doesn't teach any proof move
- The introduction says "This is definitionally true, so `rfl` suffices" — which means the learner is told the answer before starting
- Borderline acceptable as pedagogical scaffolding, but could be improved by requiring the learner to manually verify why both sides are 0 (e.g., require `rw [Finset.sum_range_succ, Finset.sum_range_zero]` first, then `rfl`)

### P2: L06 duplicates L05's statement exactly
- See coverage gap #3 above
- As a granularity issue: the world has 6 levels but effectively only 4 distinct proof experiences (L01/L02 are near-identical, L05/L06 are identical)

## 5. Learner Simulation

### Attentive Novice

**L01**: Reads the introduction, sees `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]` in the strategy section. Types it. Done. No real thinking required — the answer is in the introduction. First hint is also the answer. Learner feels guided but doesn't understand what happened.

**L02**: Same experience. Learner might try the manual path if curious. If they do, the `rw` chain works. Learner might appreciate seeing the sum unfold.

**L03**: Reads "both sides reduce to 0, try rfl". Types `rfl`. Done. Minimal engagement.

**L04 (first likely stuck point)**: This is where real learning happens. The 4-step strategy is well-explained in the intro. A novice who reads carefully can follow the steps. The step-by-step hints rescue well. After completing this, the novice understands the inductive-step template.

**L05**: The novice must now combine L03 and L04. The `induction n with` syntax might cause confusion — the novice needs to know how to handle the two branches. The intro explains the syntax. The hidden hint provides the combined `rw` chain. This is a good integration level.

**L06**: The novice re-proves L05. The paper proof table in the intro is useful reading but the level doesn't force engagement with it. The novice likely just repeats their L05 proof.

**Most likely wrong move**: In L04, trying `ring` before doing the `rw` steps. The hint doesn't explicitly warn against this — it jumps straight to the correct strategy.

**Hint rescue quality**: Good in L04 (step-by-step). Adequate elsewhere. L01/L02 hints are somewhat spoilery since the answer is already in the introduction.

### Experienced Lean User

**L01-L02**: Types `norm_num` (without arguments) and both close. Never learns about `sum_range_succ` or `sum_range_zero`. This is a missed opportunity since these lemmas are the building blocks for L03-L05.

**L03**: Types `rfl`. Done.

**L04**: May try `rw [Finset.sum_range_succ]; linarith` or similar. `linarith` works as a `ring` substitute here (verified). Not a significant exploit since the difficulty is the same.

**L05**: The experienced user will likely type the full proof in one go from the template shown in L04's conclusion. No friction.

**L06**: Exact repeat. Experienced user finds this pointless.

**Avoidable friction**: None significant for the experienced user. The levels are too easy for them but that's expected in an example world.

## 6. Course-Role Sanity

This is an **example world** (W14_ex). Its plan says: "The learner proves the classic formula sum_{i=0}^{n-1} i = n(n-1)/2 in full, and sees the connection to ordinary sigma notation."

**Is the world playing its role?** Partially. It exercises the inductive-sum proof template taught in W13 (RangeSumInduction) on a specific classic example. That's appropriate for an example world. However:

- L01/L02 behave like a tutorial on `norm_num` + sum lemmas, not like example-world levels
- L06 claims to be a transfer level but is just a repeat
- The world doesn't test whether the learner can independently apply the template — it walks them through step by step, which is more "worked example" than "example world"

If this is meant to be the learner's first independent application of the inductive-sum template, it holds the learner's hand too much. The introduction to L04 gives the complete proof strategy, and L05's intro gives the complete proof code. An example world should provide less scaffolding than the lecture world.

## 7. Technical Risks

1. **`norm_num` bypasses L01/L02 intended learning**: Bare `norm_num` (without sum-unfolding lemma arguments) closes both concrete verification levels. The learner never needs to engage with `sum_range_succ` or `sum_range_zero`. This undermines the buildup to the general proof. **Severity: P1** — the learner misses foundational understanding but the world still functions.

2. **Missing `NewTheorem` for `Finset.sum_range_zero`**: Build warning. The learner sees this lemma in hints but it's not in their theorem panel. **Severity: P1.**

3. **Missing `NewTactic` for `induction`**: Build warning. Systemic issue. **Severity: P2** (since `induction` was used in the predecessor world).

4. **`linarith` substitutes for `ring`**: After the `rw` steps in L04/L05, `linarith` closes the algebra goal. Not a significant exploit since the difficulty level is comparable and `ring` is the intended tactic. **Severity: P3** — acceptable alternative.

5. **No `omega` exploits**: Verified that `omega` cannot close any of the 6 levels. Good.

6. **No `simp`/`decide`/`trivial`/`native_decide`/`aesop`/`simp_all` exploits**: All disabled. Good.

## 8. Ranked Patch List

### P0 (blocking)
None — no single defect blocks the world entirely.

### P1 (high)

1. **Differentiate L01 and L02**: Either merge them, or disable `norm_num` on L02 and force the manual `rw` unfolding path. If forcing manual unfolding on L02, that introduces `sum_range_succ` and `sum_range_zero` as hands-on tools before they appear in L04-L05's `rw` chains. This would significantly improve the pedagogical arc.

2. **Add `NewTheorem Finset.sum_range_zero` with `TheoremDoc` in L01**: The learner needs this in their inventory since it's referenced in hints. Add alongside `Finset.sum_range_succ` (which was introduced in the predecessor world).

3. **Fix L06 to be genuine transfer**: Replace L06's statement with a different sum identity (e.g., `∑ i in Finset.range (n+1), (2*i+1) = (n+1)^2` — the sum of odd numbers). The learner transfers the same inductive-sum template to a new mathematical fact. This is real transfer. The paper-proof correspondence table stays in the introduction. Alternatively, make L06 the sum of even numbers or the sum of squares (though squares requires a harder algebra step).

4. **Add a hint in L04 for the common wrong move**: Before the first hint, add a `Branch` or initial hint that says "If you tried `ring` and it didn't close the goal, that's because `ring` can't see inside the `∑` expression. You need to unfold the sum first using `rw [Finset.sum_range_succ]`."

### P2 (medium)

5. **Strengthen L03**: Instead of just `rfl`, require the learner to manually unfold: `rw [Finset.sum_range_succ, Finset.sum_range_zero]` then `rfl` (or `ring`). This reinforces the sum-unfolding pattern before L04 uses it in the inductive step.

6. **Reduce scaffolding in L05**: The introduction to L05 gives the complete proof. For an example world (not a lecture world), the learner should have to recall the template with less hand-holding. Consider moving the complete proof code to a hidden hint rather than putting it in the introduction.

7. **Address `norm_num` bypass on L01**: Consider whether bare `norm_num` closing L01 is acceptable. If L02 is changed to force manual unfolding (patch #1), then L01 being closable by bare `norm_num` is fine — it's the "easy way" before the learner is asked to do it manually. If L01/L02 are merged, this becomes moot.

### P3 (low)

8. **Ensure `NewTactic induction` exists somewhere in the dependency chain**: This is systemic — not specific to this world. Flag for the maintainer to add in FinsetInduction or RangeSumInduction.

9. **Minor: L05 conclusion says "A new tactic: `Nat.mul_add`"**: `Nat.mul_add` is a theorem, not a tactic. The text should say "A new lemma" or "A new theorem".

## 9. What to Playtest Again After Patching

After implementing patches #1-#6:

- **L02 (if changed to manual unfolding)**: Verify the `rw` chain works, hints rescue correctly, and the learner actually engages with `sum_range_succ`/`sum_range_zero`.
- **L03 (if strengthened)**: Verify the additional `rw` step is pedagogically justified and doesn't make the base case too frustrating.
- **L06 (if replaced with new sum identity)**: Verify the new statement compiles, the proof follows the same template, hints are adequate, and the learner transfers the method rather than memorizing the specific proof.
- **Re-check exploit vectors on any changed levels**.
- **Full pass if L06 changes to a different sum identity** — the world's conclusion text will need updating.
