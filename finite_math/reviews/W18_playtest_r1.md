# W18 BinomialCoefficients -- Playtest Audit R1

**World**: BinomialCoefficients (W18, Lecture, 9 levels)
**Auditor**: playtest-auditor R1
**Build**: Compiles. `lake build` succeeds with info/warning-level messages only.

---

## 1. Overall Verdict

**NEEDS REVISION.** The world compiles and has correct DisabledTactic on all 9 levels, but suffers from three structural problems: (a) the boss is a near-duplicate of L07, (b) several levels teach only library-lemma application with no proof-move content, and (c) the `show ... from rfl` idiom in L02/L06/L09 is hostile to interactive exploration. There are no P0 exploits (the `Nat.choose_one_right` library lemma is correctly disabled in L09), but the world has significant granularity and coverage defects.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `choose_symm` gets only surface coverage (one concrete example); row sum identity is library-lemma application only; combinatorial interpretation (L07) is mislabeled |
| 2. Granularity fit | 2 | L04/L05 are near-identical single-rw levels; L07/L09 share the same statement; L07 and L08 are trivial single-step library applications |
| 3. Proof-move teaching | 2 | Only L01 and L09 teach reusable proof moves; L02-L08 are mostly "apply the right library lemma" |
| 4. Inventory design | 3 | Correct DisabledTactic, correct DisabledTheorem on boss, lemmas introduced at appropriate points |
| 5. Hint design | 2 | `show ... from rfl` hints are hostile; L01 hints are good; L07/L08 hints are spoilery (give the exact answer immediately) |
| 6. Progression | 2 | Boss is a near-duplicate of L07 rather than an integration challenge; no support fading |
| 7. Mathematical authenticity | 3 | Good intros/conclusions, combinatorial intuition well explained, concrete examples present |
| 8. Paper-proof transfer | 3 | L09 conclusion has explicit transfer moment; L07 has transfer text; other levels lack explicit transfer |
| 9. Technical fit | 3 | Builds clean; `show`/`from`/`add_comm`/`induction` not declared via NewTactic/NewTheorem (pre-existing systemic) |

**Average: 2.4** -- below the 3.0 threshold for "good."

---

## 3. Coverage Gaps

### 3a. Plan deviations

| Plan item | Actual | Gap |
|-----------|--------|-----|
| L01 "compute C(5,2)=10" | Computes C(4,2)=6 | Minor; C(4,2) is arguably better (fewer steps) |
| L07 "explain that choose n k counts k-element subsets" | Proves `choose n 1 = n` using library lemma | **The combinatorial interpretation is discussed in text only, never exercised in the proof.** L07 is mislabeled. |
| L09 "prove a non-trivial identity using Pascal's rule and induction" | Proves `choose n 1 = n` by induction | This is the same identity as L07. **Not a genuinely non-trivial identity.** |

### 3b. Coverage items with weak closure

| Item | Status | Problem |
|------|--------|---------|
| M28 (Pascal's rule) | I in L04, S in L05, G in L09 | OK but L04 is `rfl`-closable |
| M30 (Identities: symmetry, boundary) | I in L02/L06 | Only surface coverage; never retrieved unsupported |
| M31 (Row sum) | I in L08 | Library-lemma-only; never used in integration |
| C10 (k > n misconception) | W in L03 | OK |
| T7 (Combinatorial interpretation) | Discussed in L07 text | **Never exercised in a proof** -- text-only transfer |
| E17 (Concrete Pascal's triangle values) | L01, L05 | OK for compute levels |

### 3c. Missing coverage

- **`Nat.choose_symm` is never retrieved after L06.** The boss doesn't use it.
- **`Nat.sum_range_choose` is never integrated.** L08 introduces it, boss doesn't use it.
- **`Nat.choose_eq_zero_of_lt` is never retrieved after L03.** Boss doesn't use it.
- **Induction as a proof move is introduced cold in L09.** No coaching level precedes the boss.

---

## 4. Granularity Defects

### P1: L04 and L05 are near-identical

Both are single `rw [Nat.choose_succ_succ]` proofs. L04 is universally quantified (`(n : ℕ)`), L05 is concrete (`choose 6 2 = choose 5 1 + choose 5 2`). The dominant lesson is identical: "apply Pascal's rule." The concrete version (L05) is `rfl`-closable and adds no new proof move over L04.

**Recommendation**: Merge L04/L05 or replace L05 with a problem that uses Pascal's rule in a multi-step computation (e.g., compute `choose 5 3` step by step using Pascal's rule plus boundary lemmas, as a shorter version of L01 but with k > 1).

### P1: L07 and L09 share the same statement

L07: `(n : ℕ) → Nat.choose n 1 = n` via `rw [Nat.choose_one_right]`
L09: `(n : ℕ) → Nat.choose n 1 = n` via induction

The boss proves the same identity that L07 already proved with a library lemma. While the intent is different (L07 uses the library, L09 proves it from scratch), seeing the exact same statement twice is pedagogically confusing and makes the boss feel like a retread.

**Recommendation**: Change the boss to a genuinely different identity that integrates Pascal's rule, boundary lemmas, and induction. Good candidates:
- `choose n 2 = n * (n - 1) / 2` (harder, involves division)
- `choose (n+1) (k+1) = choose n k + choose n (k+1)` proved by induction (but this is just the definition)
- `choose n k + choose n (k+1) = choose (n+1) (k+1)` with both sides requiring manipulation
- A Vandermonde-style identity for small cases

### P1: L07 and L08 are trivial single-step levels

L07 is `rw [Nat.choose_one_right]`. L08 is `exact Nat.sum_range_choose 4`. Both are single-step proofs that apply a library lemma. They teach no proof move -- only the existence of a mathlib lemma.

**Recommendation**: Either (a) combine them into a single "useful library lemmas" level, or (b) make L07 actually exercise the combinatorial interpretation by proving something that requires more than a single rewrite (e.g., prove `Finset.card (Finset.filter (fun s => s.card = 1) (Finset.univ.powerset)) = n` for concrete n), or (c) make L08 a multi-step level that builds up to the row sum.

---

## 5. Statement Exploitability

### rfl exploits (P2, cannot disable)

All 6 concrete levels (L01, L02, L03, L05, L06, L08) are closable by `rfl`. This is inherent to concrete Nat.choose computations and cannot be fixed without restructuring to universally-quantified statements. **Accept as P2.**

### Disabled tactics (verified correct)

All 9 levels disable: `trivial decide native_decide simp aesop simp_all`. Correct and consistent.

### L09 DisabledTheorem (verified correct)

L09 correctly disables `Nat.choose_one_right`, preventing the library-lemma shortcut.

### L04 definitional equality (P2)

`Nat.choose (n + 1) 1 = Nat.choose n 0 + Nat.choose n 1` is true by `rfl` because `choose_succ_succ` is the definition. Cannot be fixed without changing the statement. **Accept as P2.**

---

## 6. Interactive Proof Quality

### P1: `show ... from rfl` idiom (L02, L06, L09)

The pattern `rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_zero_succ]` is hostile to interactive exploration:
- The learner must type the entire compound expression correctly before getting any feedback
- `show ... from rfl` is an advanced Lean idiom not taught in NNG4 or earlier worlds
- It provides no intermediate proof-state change

This appears in:
- **L02**: `rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_zero_succ]`
- **L06**: `rw [show (5 : ℕ) = 7 - 2 from rfl, Nat.choose_symm]`
- **L09**: `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`

**Fix**: Replace with two-step approach:
```
have h : (3 : ℕ) = 2 + 1 := by omega
rw [h, Nat.choose_zero_succ]
```
This is interactive (each step gives feedback), uses only taught tactics (`have`, `omega`, `rw`), and is self-explanatory.

### L01 proof length (Acceptable)

L01 has 11 `rw` steps. This is long but each step is interactive and produces visible progress. The learner sees the recursion unfold step by step. This is acceptable for a first level whose purpose is to make the recursion concrete.

---

## 7. Learner Simulation

### Attentive novice

**First stuck point**: L02, final step. The `show (3 : ℕ) = 2 + 1 from rfl` idiom will be completely opaque. The learner has never seen `show ... from rfl` and the hint just gives the answer without explaining the idiom. The learner will likely try `rw [Nat.choose_zero_succ]` directly and find it doesn't pattern-match (because `3` is not syntactically `k + 1`).

**Most likely wrong move**: At L06, trying `rw [Nat.choose_symm]` without first rewriting `5` to `7 - 2`. The error message will be unhelpful. The hint eventually rescues, but the `show` idiom will still be confusing.

**Hint rescue quality**: L01 hints are excellent (layered, context-appropriate). L02/L06 hints are poor for the `show` step. L07/L08 hints are spoilery (immediate answer). L09 hints are good (progressive).

**Lesson legibility**: L01 (recursion) is clear. L03 (apply + omega) is clear. L04/L05 (single rw) -- lesson is clear but trivial. L06 -- the symmetry idea is clear but the Lean execution is opaque. L07/L08 -- no real lesson beyond "this library lemma exists." L09 -- induction lesson is clear.

### Experienced Lean user

**Avoidable friction**: The `show ... from rfl` pattern when `have h : ... := by omega; rw [h, ...]` would be cleaner and more standard.

**Alias gaps**: None significant. `Nat.choose_symm` direction matches the rewrite direction needed.

**Inventory clutter**: Low. Each level introduces 0-1 new theorems.

**Forced verbosity**: L01 is forced-verbose (11 rw steps) but deliberately so. L02/L06 `show` trick is forced-opaque rather than forced-verbose.

**rfl shortcut**: An experienced user will notice that all concrete levels are closable by `rfl`. This is inherent and acceptable.

---

## 8. Boss Integrity (L09)

### Seeded subskills

| Subskill | Where seeded | Status |
|----------|-------------|--------|
| `induction n with` | Not seeded in this world | **DEFECT**: Induction is used extensively in prior worlds (W14+), but this world has no coaching level |
| `Nat.choose_succ_succ` | L01, L04, L05 | OK -- well practiced |
| `Nat.choose_zero_right` | L01, L02 | OK |
| `Nat.choose_zero_succ` | L02 | OK -- but only via `show` trick |
| `add_comm` | Not introduced | **DEFECT**: Used in boss but never taught or practiced |
| `show ... from rfl` | L02, L06 | Used in boss base case -- problematic idiom |

### Closure quality: WEAK

The boss uses `induction` and `add_comm`, neither of which is introduced in this world. `induction` is taught in prior worlds (RangeSumInduction, etc.) but the plan does not list it as a prerequisite move for W18. `add_comm` is never formally introduced anywhere in the course.

### Integration quality: WEAK

The boss integrates only Pascal's rule + boundary conditions. It does NOT use:
- `Nat.choose_symm` (taught in L06)
- `Nat.choose_eq_zero_of_lt` (taught in L03)
- `Nat.sum_range_choose` (taught in L08)

A good boss should integrate more of the world's repertoire.

### Surprise burden: MODERATE

Induction is not new for the course, but it is new for this world. The learner must recall induction from 4+ worlds ago. The `add_comm` step is a minor surprise.

### Can the learner explain why the proof works? YES

The inductive structure is clear and the conclusion includes an explicit paper-proof transfer.

---

## 9. Course-Role Sanity

| Level | Intended role | Actual role | Miscast? |
|-------|--------------|-------------|----------|
| L01 | Worked example | Worked example | No |
| L02 | Practice (boundary) | Practice | No |
| L03 | Warning/misconception | Warning | No |
| L04 | First-contact (Pascal's rule) | Trivial application | **Yes** -- `rfl`-closable, no real engagement |
| L05 | Supported practice | Trivial repeat | **Yes** -- identical proof move to L04 |
| L06 | First-contact (symmetry) | First-contact | No, but opaque execution |
| L07 | Example/transfer (counting) | Trivial library application | **Yes** -- title says "counting subsets" but proof is just `rw [choose_one_right]` |
| L08 | First-contact (row sum) | Trivial library application | **Yes** -- no engagement with the identity |
| L09 | Boss | Retread of L07 | **Yes** -- same statement as L07 |

Five of nine levels are miscast to some degree.

---

## 10. Technical Risks

1. **Build warnings (info-level, pre-existing systemic)**: Missing TacticDoc for disabled tactics. These docs exist in earlier worlds. Not specific to W18.

2. **Build warning**: `No world introducing show, from, add_comm, induction but required by BinomialCoefficients`. The `show`/`from` issue is caused by the `show ... from rfl` idiom. If this idiom is removed (recommended), the warning goes away.

3. **Missing TheoremDoc**: `Nat.choose_one_right` is disabled in L09 but its TheoremDoc is in L07. The build warns because the DisabledTheorem in L09 refers to a theorem whose doc is defined in a different level file. This is cosmetic but should be noted.

---

## 11. Ranked Patch List

### P0 (Blocking)

None. No exploits bypass disabled tactics.

### P1 (High -- must fix before shipping)

| # | Issue | Levels | Fix |
|---|-------|--------|-----|
| 1 | **Boss is a duplicate of L07** | L09, L07 | Redesign boss to prove a different identity that integrates symmetry, Pascal's rule, and boundary conditions. E.g., prove `choose (n+1) 2 = choose n 2 + n` by induction, or prove the alternating sum identity `sum (-1)^k * choose n k = 0` for n > 0. |
| 2 | **`show ... from rfl` idiom** | L02, L06, L09 | Replace with `have h : ... := by omega` then `rw [h, ...]`. More interactive, uses taught tactics only. |
| 3 | **L04/L05 near-identical** | L04, L05 | Merge into one level or make L05 a multi-step computation that uses Pascal's rule plus boundary lemmas. |
| 4 | **L07/L08 are trivial single-step levels** | L07, L08 | Either (a) combine, or (b) give them multi-step proofs that build toward the library lemma rather than just citing it. E.g., L07 could prove `choose n 1 = n` by induction (which is currently the boss), and then L08 could verify the row sum for a specific n by expanding each term. |
| 5 | **L07 mislabeled** | L07 | Title and intro claim "counting subsets" but the proof has nothing to do with counting. Either rename to match the actual content ("choose n 1 = n") or redesign to exercise the combinatorial interpretation. |
| 6 | **Boss doesn't integrate symmetry, k>n, or row sum** | L09 | Redesign boss to require at least 3 distinct moves from the world repertoire, including `choose_symm` or `choose_eq_zero_of_lt`. |

### P2 (Medium -- fix if possible)

| # | Issue | Levels | Fix |
|---|-------|--------|-----|
| 7 | All concrete levels closable by `rfl` | L01, L02, L03, L05, L06, L08 | Accept. Cannot disable `rfl`. |
| 8 | L04 closable by `rfl` (definitional) | L04 | Accept. The statement is definitional. |
| 9 | `add_comm` not formally introduced | L09 | Add `NewTheorem add_comm` in L09 or in an earlier level of this world. |
| 10 | No coaching level for induction in this world | L09 | If boss continues to use induction, add a coaching level before it (e.g., L08.5 proving a simpler identity by induction). |

### P3 (Low)

| # | Issue | Fix |
|---|-------|-----|
| 11 | Plan says C(5,2)=10 but L01 does C(4,2)=6 | Accept; C(4,2) is more manageable. Update plan to match. |
| 12 | `show`/`from` never declared as NewTactic | Remove `show...from rfl` idiom (fixes the root cause). |

---

## 12. What to Playtest Again After Patching

1. **The redesigned boss** -- verify it integrates 3+ moves, is not `rfl`-closable, and has layered hints.
2. **The replacement for `show ... from rfl`** -- verify `have h := by omega; rw [h, ...]` gives good intermediate feedback in the game server.
3. **Any merged or restructured levels** (L04/L05, L07/L08) -- verify the new versions have appropriate difficulty and hint coverage.
4. **Re-check all DisabledTactic/DisabledTheorem** after restructuring -- any new boss identity needs its matching library lemma disabled.
