# Playtest Audit: PsetBigOp

**World**: PsetBigOp (W18)
**Type**: Problem Set
**Pset partner for**: BigOpIntro (W14), BigOpAlgebra (W15), FinsetInduction (W16), SummationFormulas (W17)
**Levels**: 8 (L01-L08)

---

## 1. Overall Verdict: PASS

A well-constructed pset with fresh surface forms, proper retrieval-to-transfer-to-integration progression, well-blocked exploits, and a boss that integrates 6 distinct moves. No P0 defects found.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Covers all four prerequisite worlds; `sum_range_succ` not tested (range-based induction fully in SummationFormulas; pset focuses on finset induction — acceptable) |
| Granularity fit | 4 | Each level has one dominant lesson; clean retrieval → transfer → integration arc |
| Proof-move teaching | 3 | Conclusions explain the "why" well; introductions state strategy; pset-appropriate scaffolding |
| Inventory design | 4 | No new inventory items (correct for pset); disabled theorems are well-targeted per level |
| Hint design and recoverability | 3 | Mostly hidden (appropriate for pset); layered on boss; L01 could benefit from a visible strategy hint |
| Worked example → practice → transfer → boss | 4 | Clear L01-L05 retrieval, L06 transfer, L07 integration, L08 boss |
| Mathematical authenticity | 3 | Boss conclusion explains the algebraic identity clearly; Fubini analogy in L04 is good; conclusions connect to broader math |
| Paper-proof transfer | 3 | Conclusions consistently connect Lean moves to mathematical reasoning; boss explains the `have+ring+omega` bridge well |
| Technical fit and maintainability | 4 | Builds clean; no import issues; consistent disabled-tactic baselines; TheoremTab present everywhere |

**Average**: 3.44
**Minimum**: 3

---

## 3. Summary Statistics

- Average score: 3.44
- Minimum score: 3 (Coverage closure, Proof-move teaching, Hint design, Mathematical authenticity, Paper-proof transfer)
- No score below 2
- No automatic red flags triggered

---

## 4. P0 Defects (Blocking)

None.

---

## 5. P1 Defects (High Priority)

None.

---

## 6. P2 Defects (Medium)

### P2-1: L01 is structurally very similar to BigOpIntro L05

L01 proves `∑ x ∈ {2, 5, 8}, f x = 18` given function value hypotheses. BigOpIntro L05 proves `∑ x ∈ {10, 20, 30}, f x = f 10 + f 20 + f 30`. The core proof structure is identical (have non-membership, sum_insert, have non-membership, sum_insert, sum_singleton). The only new elements are hypothesis substitution (`rw [hf2, hf5, hf8]`) and final arithmetic (`omega`).

**Risk**: Learner feels they're repeating BigOpIntro rather than being tested.
**Suggestion**: Either (a) make the finset construction less direct — e.g., give `s` as hypothesis with `hs : s = {2, 5, 8}` so the learner must also unfold the finset, or (b) use a different surface form entirely — e.g., compute a sum over `Finset.range 4` using `sum_range_succ` peeling (which would also retrieve SummationFormulas).

### P2-2: L07 Branch 1 has no intermediate hints

Branch 1 (all rewrites in one chain + `ring`) has zero hints. If a learner takes this path and gets stuck after the `rw` chain (e.g., `ring` doesn't close because of a typo in the rewrite list), there's no rescue. The visible hint before the Branch describes the full strategy, which partially mitigates this, but a hint after the `rw` saying "close with `ring`" would be consistent with Branch 2.

### P2-3: L02 conclusion explains `•` notation but it's not the first time `•` appears

The conclusion says "For natural numbers, `n • m` is `n * m`." If `•` was introduced in BigOpAlgebra L03 (sum_const), this explanation is redundant retrieval — which is fine for a pset, but the wording suggests first-contact framing. Minor.

---

## 7. Coverage Gaps

### Range-based induction not tested

SummationFormulas heavily uses `sum_range_succ` / `sum_range_zero` with natural number induction. PsetBigOp exclusively uses finset induction (`Finset.induction_on`) with `sum_insert`. This is a deliberate design choice (the pset focuses on the newer skill — finset induction), but it means `sum_range_succ`-based proofs get no pset retrieval.

**Impact**: Low. SummationFormulas itself provides extensive practice. The boss uses `have + ring + omega` (a SummationFormulas technique) in a finset induction context, which is genuine transfer.

### No `sum_congr` retrieval

`sum_congr` was taught in BigOpIntro (L08) and retrieved in BigOpAlgebra (L05), but is not tested in this pset (and is actively disabled on the boss). Since it's a rewriting-under-binder skill that has had supported practice, this is acceptable but noted.

---

## 8. Granularity Defects

None. The 8-level structure with clear retrieval (L01-L05), transfer (L06), integration (L07), and boss (L08) is well-calibrated. No level is overbroad or overfine.

---

## 9. Learner Simulation Notes

### Attentive Novice

- **L01**: First stuck point is the non-membership proof. The `(2 : ℕ)` type annotation may trip them up. Hidden hint covers the exact pattern. Recovery works.
- **L02**: The "order matters" warning in the introduction is helpful. If the learner applies `sum_union` first, they get a harder goal (4 terms). The introduction explicitly warns against this. Good pedagogical design.
- **L03**: A novice might try `sum_add_distrib` + `sum_const` first (the algebraic approach from BigOpAlgebra). These are disabled, so the learner must switch to induction. This is the right forcing behavior for a pset.
- **L05**: The `← sum_filter` (backward rewrite) is the key retrieval. `← rw` was explicitly taught in FinsetImage L20, and `sum_filter` backward was mentioned in BigOpAlgebra L07's conclusion. The hint shows the exact syntax. Recoverable.
- **L08 Boss**: Introduction explains the full strategy (induction + peel + have + ring + omega). Hints are well-layered: visible strategic hint, then hidden code hint at each step. The `have` technique was practiced in SummationFormulas. A novice who completed SummationFormulas should be able to assemble this proof with hint support.

### Experienced Lean User

- **L01**: Tedious but appropriate for retrieval. An experienced user will complete it in under a minute.
- **L04**: Clean three-step proof. No friction.
- **L07**: Both `calc` and `rw` paths are accepted. Experienced users will appreciate the flexibility.
- **L08**: The natural-subtraction difficulty is real and well-placed. The `have + ring + omega` bridge is elegant. An experienced user who knows this pattern will find the boss satisfying.

---

## 10. Pset Integrity Notes

### Fresh surface form: PASS (with minor concern on L01)

| Level | Source world | Fresh? | Notes |
|-------|-------------|--------|-------|
| L01 | BigOpIntro L05 | Borderline | Same proof structure, function-value substitution is only new element |
| L02 | BigOpAlgebra L01+L03+L06 | Yes | New combination of sum_add_distrib + sum_const + sum_union |
| L03 | FinsetInduction L05 | Yes | Different summand (f x + 1 vs f x + f x), introduces cardinality |
| L04 | BigOpAlgebra L08 | Yes | Combines sum_add_distrib + sum_comm (lecture only had bare sum_comm) |
| L05 | BigOpAlgebra L07 | Yes | Backward direction of sum_filter, combined with sum_add_distrib |
| L06 | FinsetInduction L07-L08 | Yes | Different identity; introduces exponent in cardinality |
| L07 | BigOpAlgebra L14 | Yes | Mixed sum+product decomposition; both calc and rw accepted |
| L08 | SummationFormulas L12 | Yes | Transfers telescoping pattern from range to finset induction |

### Reduced scaffolding: PASS

All hints hidden except boss strategic hints. Introductions state the tools needed but don't walk through the proof. Appropriate for a pset.

### Real retrieval: PASS

Each level requires the learner to recall and apply skills from specific prerequisite worlds. The conclusions explicitly reference which worlds are being retrieved.

### Not cloning lecture material: PASS (with P2-1 note on L01)

---

## 11. Boss Integrity Notes (L08)

### Seeded subskills: PASS

| Boss move | Where seeded in PsetBigOp | Where first taught |
|-----------|--------------------------|-------------------|
| `Finset.induction_on` | L03, L06 | FinsetInduction L01 |
| `sum_insert ha` | L01, L03 | BigOpIntro L03 |
| `card_insert_of_notMem ha` | L03, L06 | FinsetInduction L04 |
| `have ... := by ring` | — | SummationFormulas L05 |
| `omega` with IH | L03 | SummationFormulas L05 |
| `sum_empty`/`card_empty`/`ring` (base) | L03, L06 | FinsetInduction L02/L05 |

All boss moves are seeded either in this world or in prerequisites. No untaught micro-skills.

### Integration quality: PASS

The boss integrates 6 distinct moves from 3 different worlds (BigOpIntro, FinsetInduction, SummationFormulas). The natural-subtraction twist makes this genuinely harder than any single prerequisite level.

### Surprise burden: LOW

The only "new" element is natural subtraction inside a finset sum (vs. inside a range sum in SummationFormulas L12). The strategy is explained in the introduction. The `have + ring + omega` technique is identical to what was practiced.

### Can a learner explain why the proof works? YES

The conclusion explains: each term `(f(x)+1)^2 - f(x)^2 = 2f(x) + 1`, so `∑(2f(x) + 1) = 2∑f(x) + |s|`. The algebraic identity is stated and the connection to the telescoping/difference-of-squares pattern is made clear.

---

## 12. Technical Risks

### Exploit analysis: No unblocked exploits found

| Level | Key disabled theorems | Key disabled tactics | Intended path forced? |
|-------|----------------------|---------------------|----------------------|
| L01 | sum_cons, sum_pair | decide, simp, norm_num | Yes — must peel manually |
| L02 | sum_eq_card_nsmul, sum_nsmul | decide, simp, norm_num | Yes — must use sum_add_distrib+sum_const+sum_union |
| L03 | sum_add_distrib, sum_const, card_eq_sum_ones | decide, simp, norm_num | Yes — must use induction |
| L04 | sum_pair | decide, simp, norm_num | Yes — must use sum_add_distrib+sum_comm |
| L05 | sum_ite | decide, simp, norm_num | Yes — must use ← sum_filter |
| L06 | prod_const, prod_mul_distrib | decide, simp, norm_num | Yes — must use induction |
| L07 | sum_pair, prod_pair | decide, simp, norm_num | Yes — must use sum_add_distrib+prod_mul_distrib |
| L08 | mul_sum, sum_mul, sum_add_distrib, sum_congr | decide, simp, norm_num | Yes — must use induction+have+ring+omega |

No lattice alias exploits relevant (levels don't involve Finset ∪/∩).
No `fin_cases`/`ext`/`interval_cases`/`by_cases` exploits (all disabled).

---

## 13. Ranked Patch List

1. **P2-1**: Consider freshening L01's surface form to avoid structural similarity with BigOpIntro L05. Options: (a) require finset unfolding from a hypothesis, (b) use a different proof structure (e.g., sum over `range` with `sum_range_succ`).
2. **P2-2**: Add a `Hint (hidden := true) "Close with ring."` inside L07 Branch 1 after the `rw` chain.
3. **P2-3**: Minor wording adjustment in L02 conclusion to frame `•` as retrieval rather than introduction.

---

## 14. What to Playtest Again After Patching

- If L01 surface form is changed: re-check that the new version still tests `sum_insert` peeling and doesn't introduce new skills.
- If L07 Branch 1 gets a hint: verify the hint fires in the right goal state.
- No structural changes needed — the world is sound.
