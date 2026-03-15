# W18 BinomialCoefficients -- Playtest Audit (Round 2)

**World**: BinomialCoefficients (W18, Lecture, 9 levels)
**Focus**: Verify R1 fix (boss exploitable by `exact Nat.choose_one_right n`), check for remaining issues.
**Prerequisite**: Factorials (W17)

---

## 1. Overall Verdict

**CONDITIONAL PASS, P1** -- The R1 boss exploit is fixed. However, `norm_num` is not disabled and one-shots five of the nine levels (L01, L02, L03, L05, L06), all of which have concrete numerical goals. The `show ... from rfl` pattern used in L02, L06, and L09 is a hidden prerequisite leak -- it is never taught before this world and represents an untaught term-mode proof construct embedded inside tactic calls.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 2 | Many levels are single-step library applications; proof-move coverage weak |
| Granularity fit | 3 | Each level has a clear dominant lesson, world is coherent |
| Proof-move teaching | 2 | L01 teaches recursive unfolding; L09 teaches induction; L02-L08 are mostly API lookups |
| Inventory design | 3 | Theorems unlocked at right times, docs present. `Nat.choose_self` used in L01 before declared in L02 (minor) |
| Hint design / recoverability | 3 | Hints present at most steps, hidden rescue hints available. `show ... from rfl` hints give the answer without explaining the pattern |
| Worked example -> practice -> transfer -> boss | 2 | L01 is a good worked example, L09 is a real boss, but L02-L08 are mostly "apply library lemma" with no genuine practice |
| Mathematical authenticity | 3 | Good mathematical content, nice combinatorial explanations, L03 misconception level well-placed |
| Paper-proof transfer | 3 | Transfer moments in L07, L08, L09 conclusions are solid |
| Technical fit / maintainability | 3 | Compiles, clean structure, proper disabled tactic baseline |

**Average: 2.67** (below 3.0 threshold; two categories at 2)

---

## 3. R1 Fix Verification

**R1 issue**: L09 boss exploitable by `exact Nat.choose_one_right n`.
**Fix applied**: `DisabledTheorem Nat.choose_one_right` added to L09.
**Verification**: Fix is effective.

- `Nat.choose_one_right` is the only library lemma that directly proves `choose n 1 = n` for arbitrary `n`.
- No alias exists in current mathlib (no `Nat.choose_one`, no `Nat.choose_one_left` that would help).
- The statement is universally quantified over `n`, so `norm_num`, `rfl`, `omega`, and `ring` cannot close it.
- Indirect paths (via `Nat.choose_mul_factorial_mul_factorial` + factorial manipulation) require substantial multi-step reasoning and are not one-shot exploits.
- The only viable proof path is induction + recursive lemmas, which is the intended approach.

**Verdict on R1 fix: CONFIRMED EFFECTIVE.**

---

## 4. Statement Exploitability (Level-by-Level)

### L01: `Nat.choose 4 2 = 6`
- **norm_num**: NOT disabled. Likely closes the goal in one step (Nat.choose is computable, norm_num evaluates computable functions on numerals). **P1** -- bypasses the entire recursive unfolding lesson.
- **rfl**: Cannot be disabled. May close the goal via kernel reduction. **P2** -- accepted pattern per project conventions.
- **decide/native_decide/trivial**: Disabled. OK.

### L02: `Nat.choose 4 0 + Nat.choose 4 4 + Nat.choose 0 3 = 2`
- **norm_num**: Likely closes in one step. **P1**.
- Same rfl/decide analysis as L01.

### L03: `Nat.choose 3 5 = 0`
- **norm_num**: Likely closes in one step. **P1**.
- Intended lesson (apply + omega) bypassed.

### L04: `(n : Nat) -> Nat.choose (n + 1) 1 = Nat.choose n 0 + Nat.choose n 1`
- **norm_num**: Cannot close (universally quantified). Safe.
- No library lemma one-shots this (it IS `choose_succ_succ`). Safe -- the intended proof IS the one-step rewrite.

### L05: `Nat.choose 6 2 = Nat.choose 5 1 + Nat.choose 5 2`
- **norm_num**: Likely closes in one step (all concrete numerals on both sides). **P1**.

### L06: `Nat.choose 7 5 = Nat.choose 7 2`
- **norm_num**: Likely closes in one step. **P1**.
- Intended lesson (choose_symm + omega) bypassed.

### L07: `(n : Nat) -> Nat.choose n 1 = n`
- **norm_num**: Cannot close (universally quantified). Safe.
- **Nat.choose_one_right**: Available (not disabled here). This is the intended solution -- the level's lesson IS to apply this lemma. Not an exploit.

### L08: `sum m in range 5, choose 4 m = 2^4`
- **norm_num**: The sum over a concrete finset range with concrete choose values may or may not reduce under norm_num. Probably not without simp lemmas to evaluate the sum. **P2 at most**.
- Intended proof (`exact Nat.sum_range_choose 4`) is a one-shot library call, which is the designed lesson.

### L09 (Boss): `(n : Nat) -> Nat.choose n 1 = n`
- **Nat.choose_one_right**: Disabled. Fix confirmed.
- **norm_num**: Cannot close (universally quantified). Safe.
- **omega/ring/rfl**: Cannot close. Safe.
- No alternative one-shot exploit found.

**Summary**: `norm_num` exploits on L01, L02, L03, L05, L06 are **P1**. These are the five levels with concrete numerical goals. Adding `norm_num` to the DisabledTactic list on these levels would fix all five.

---

## 5. Interactive Proof Quality

### `show ... from rfl` pattern -- **P1 hidden prerequisite leak**

The pattern `rw [show (3 : Nat) = 2 + 1 from rfl, Nat.choose_zero_succ]` appears in:
- L02 (line 57)
- L06 (line 50)
- L09 boss, base case (line 63)

This construct is never taught before W18. It is not used in any prior world in the course. The `show X from proof` syntax is a term-mode proof embedded inside a tactic argument -- it is fundamentally different from the `show` tactic (which changes the goal display). The learner encounters this for the first time in a hint with no explanation of what it does or why it is needed.

**Why it matters**: The L02 hint says "Try `rw [show (3 : Nat) = 2 + 1 from rfl, Nat.choose_zero_succ]`" -- but the learner has never seen `show ... from ...` before. They must copy the exact syntax to proceed. This is a spoiler hint (gives the exact move) masking a hidden prerequisite (the syntax pattern). If the learner tries to figure out the step independently, they have no way to discover the `show ... from rfl` trick.

**Alternative approaches**: The levels could avoid this pattern entirely:
1. Use `have h : (3 : Nat) = 2 + 1 := rfl` then `rw [h, Nat.choose_zero_succ]` -- this uses only the taught `have` tactic and `rfl`.
2. Use `norm_num` or `omega` to close residual arithmetic after partial rewriting (but norm_num is the exploit tactic, so this creates a tension).
3. Redesign the statement to avoid the numeral-matching issue (e.g., use `Nat.choose 0 (k + 1)` with a concrete `k`).

### L01 hint gaps

L01 has 10 rewrite steps. Hints appear after steps 1, 2, 3, and 6. Steps 4-5 and 7-10 have no individual hints. The steps are pattern-repetitive, so experienced learners will manage, but novices may feel unsupported in the second half.

---

## 6. Coverage Gaps

| Gap | Severity |
|-----|----------|
| `norm_num` exploits 5 concrete levels | P1 |
| `show ... from rfl` hidden prerequisite | P1 |
| `Nat.choose_self` used in L01 proof but not in L01's `NewTheorem` (declared in L02) | P2 -- minor discoverability issue for L01, mitigated by hints |
| Boss only integrates L01-L02 material (choose_succ_succ, choose_zero_right, choose_zero_succ); L03-L08 content is never tested | P2 -- noted in R1 enrichment, not a playtest-blocking issue |
| `add_comm` used in L09 but never declared via `NewTheorem` anywhere in the course | P2 -- learner can use `omega` as alternative |

---

## 7. Granularity Defects

None blocking. The 9-level structure is coherent:
- L01: Recursive computation (worked example)
- L02: Boundary values (practice)
- L03: k > n case (misconception)
- L04: Pascal's rule, general (first-contact)
- L05: Pascal's rule, concrete (practice)
- L06: Symmetry (first-contact)
- L07: choose n 1 = n (first-contact)
- L08: Row sum (first-contact)
- L09: Boss (integration)

The enrichment review correctly notes that L04, L05, L07, L08 are single-step levels. This is a coverage/depth concern, not a granularity defect.

---

## 8. Learner Simulation

### Attentive novice

**L01**: Works well. Hints guide through recursive unfolding step by step. First stuck point is likely around step 4-5 where hints thin out, but the pattern (try choose_succ_succ, then boundary lemmas) is established by then. The `Nat.choose_self` usage without prior introduction is a minor surprise -- the learner sees it in a hint and copies it.

**L02**: The first two steps (choose_zero_right, choose_self) are fine. The third step forces `rw [show (3 : Nat) = 2 + 1 from rfl, Nat.choose_zero_succ]`. **This is the first stuck point.** The novice sees a goal with `Nat.choose 0 3` and knows `choose_zero_succ` applies to `choose 0 (k+1)`, but Lean doesn't recognize `3` as `2 + 1` for matching. The hint gives the exact code, but the novice has never seen the `show ... from rfl` syntax. They copy it without understanding. **Recovery**: copying works, but the lesson (why numerals need manual reshaping for pattern matching) is invisible.

**L06**: Same issue with `show (5 : Nat) = 7 - 2 from rfl`. Novice copies the hint.

**L09 boss**: The induction framework is clear (hints at every step). The base case reuses the `show ... from rfl` pattern from L02 -- by now the novice has seen it twice and may be comfortable copying it, but still does not understand it.

**Overall novice experience**: Passable but fragile. The `show ... from rfl` pattern creates three moments of "copy without understanding." The concrete computation levels (L01-L03, L05-L06) are at risk of being norm_num'd by curious novices who try their full tactic repertoire.

### Experienced Lean user

**L01-L05**: Experienced user types `norm_num` and clears the level instantly. No engagement with the recursive structure. **This is a failure of the level design for this audience segment.**

**L06**: Similarly, `norm_num` closes it.

**L07**: `exact Nat.choose_one_right n` or `rw [Nat.choose_one_right]`. Clean.

**L08**: `exact Nat.sum_range_choose 4`. Clean.

**L09**: With `choose_one_right` disabled, the experienced user does the induction. They would likely use `omega` for the base case and `omega` or `linarith` for the final step instead of `add_comm`. This works fine.

**Friction points**: The `show ... from rfl` pattern is familiar to an experienced Lean user but feels inelegant. They might prefer `change Nat.choose 0 (0 + 1) = 0` or `conv => lhs; rw [show ...]`.

---

## 9. Boss Integrity

### L09: C(n, 1) = n by induction

**Seeded subskills**:
- `induction`: Assumed from NNG4 prerequisite. OK.
- `choose_succ_succ`: Introduced L01, practiced L04-L05. OK.
- `choose_zero_right`: Introduced L01, practiced L02. OK.
- `choose_zero_succ`: Introduced L01, practiced L02-L03. OK.
- `add_comm`: NNG4 prerequisite, not formally declared. OK (omega alternative exists).
- `show ... from rfl`: Used in L02 and L06 but never formally taught. **Hidden prerequisite leak** (P1).

**Closure quality**: All four rewrite lemmas in the boss proof are taught and practiced. The induction pattern is assumed from NNG4. The `show ... from rfl` step in the base case is the only untaught element.

**Integration quality**: The boss integrates material from L01-L02 only. It does not exercise symmetry (L06), the k > n case (L03), counting interpretation (L07), or row sum (L08). This was noted in R1 enrichment. For the playtest audit, the boss is functional but narrow.

**Surprise burden**: None. The proof has a clear structure (base case + inductive step), and every step has a hint.

**Can the learner explain why the proof works?** Yes -- the conclusion and transfer moment articulate the proof strategy clearly. The induction structure maps directly to the paper proof.

---

## 10. Technical Risks

| Risk | Severity |
|------|----------|
| `norm_num` not disabled on L01-L03, L05-L06 | P1 |
| `show ... from rfl` untaught pattern used in L02, L06, L09 | P1 |
| `rfl` may close concrete numerical choose goals | P2 (accepted) |
| `Nat.choose_self` used before declared | P2 (minor) |
| `add_comm` not in `NewTheorem` | P2 (omega alternative) |

---

## 11. Ranked Patch List

### P1 -- Must fix

1. **Add `norm_num` to DisabledTactic on L01, L02, L03, L05, L06.** These five levels have concrete numerical goals that `norm_num` likely one-shots. The intended lessons (recursive unfolding, boundary lemmas, symmetry) are entirely bypassed. Change each level's DisabledTactic line from:
   ```
   DisabledTactic trivial decide native_decide simp aesop simp_all
   ```
   to:
   ```
   DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
   ```
   L04, L07, L08, L09 have universally quantified statements and do not need this change.

2. **Address the `show ... from rfl` hidden prerequisite.** Three options (in order of preference):
   - **(a)** Replace all `show ... from rfl` occurrences with `have h : (3 : Nat) = 2 + 1 := rfl` followed by `rw [h, Nat.choose_zero_succ]`. The `have` tactic is taught from NNG4 and `rfl` is basic. This decomposes the opaque one-liner into two familiar steps.
   - **(b)** Add a short explanation in L02's introduction about why numeral reshaping is sometimes needed and what the `show ... from rfl` idiom does.
   - **(c)** Redesign the statements to avoid the numeral-matching issue entirely.

### P2 -- Should fix

3. **Add `Nat.choose_self` to L01's `NewTheorem` declaration** (or move its usage to after L02). Currently L01 uses it in the proof but it is only declared in L02.

4. **Add `omega` as an alternative in L09's final hint.** The hint says "Use `add_comm`" but `omega` is a taught tactic that also closes `1 + n = n + 1`. The hidden hint should mention both options.

### P3 -- Nice to have

5. **Improve L01 hint coverage in steps 4-10.** The second half of the proof has fewer hints. Adding a hint after step 7 ("Almost there -- continue with boundary lemmas for any remaining terms") would help novices.

---

## 12. What to Playtest Again After Patching

- **L01, L02, L03, L05, L06**: Verify `norm_num` is properly disabled and the levels still have valid intended proofs.
- **L02, L06, L09**: Verify the `show ... from rfl` replacement (if option (a) is chosen) compiles and the hints are coherent.
- **L09**: Verify no new exploits emerged. Specifically, if `norm_num` is disabled on L09 (not necessary for the universally quantified statement, but for consistency), verify the base case still works.

---

## Summary

The R1 boss exploit (`exact Nat.choose_one_right n`) is confirmed fixed by `DisabledTheorem Nat.choose_one_right` on L09. Two P1 issues remain: (1) `norm_num` is not disabled on five concrete-goal levels and likely one-shots them, and (2) the `show ... from rfl` pattern is an untaught term-mode construct used in three levels. Both are straightforward to fix. After these patches, the world should pass a clean audit.
