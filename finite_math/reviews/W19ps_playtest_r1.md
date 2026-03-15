# W19_ps CombinatorialPset -- Playtest Audit R1

## 1. Overall verdict

**Needs revision.** The world compiles and the pset structure is sound, but it has one P1 defect (boss introduction spoils the proof plan), one P1 defect (L05/L06 are near-clones of lecture material rather than genuine transfer), and multiple P2 issues (rfl exploits on 5 of 7 levels, `mul_one` hidden prerequisite in the boss). The pset role is weakened by the concrete levels being closeable by `rfl` and the transfer levels requiring only one-liner lemma applications.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | M28, M29, M30, M31 retrieved; T7, T10 transfer present |
| Granularity fit | 3 | Each level has a clear dominant lesson; 7 levels is right-sized |
| Proof-move teaching | 2 | Boss intro gives the full proof plan; L05/L06 are one-liners |
| Inventory design | 3 | No new items introduced (correct for pset); all used items were taught |
| Hint design | 3 | All hints hidden (correct for pset); hints are rescue-quality |
| Progression | 2 | L05/L06 don't test retrieval -- they're clones with a library lemma |
| Mathematical authenticity | 3 | Good transfer moments in conclusions; concrete checks throughout |
| Paper-proof transfer | 3 | Every level has a transfer moment; L05/L06 have dual-proof discussion |
| Technical fit | 3 | Builds clean; standard DisabledTactic set; no missing docs |

**Average: 2.8** (below the 3.0 threshold for "good")

## 3. Coverage gaps

- **No coverage gaps for the planned items.** M28 (T), M30 (T), M31 (T), M29 (R), T7 (T), T10 (T) are all present as planned.
- Minor: `mul_one` is used in the boss but was never formally introduced via `NewTheorem` anywhere in the course. It's a basic NNG4 lemma so this is P2 severity.

## 4. Granularity defects

### P1-01: L05 and L06 are near-clones of lecture material

**L05** proves `sum k in range 7, choose 6 k = 64`. The proof is `exact Nat.sum_range_choose 6`. This is the same operation as BinomialTheorem L05 (which uses `Nat.sum_range_choose n`) -- just instantiated at `n = 6`. The learner applies the same lemma with the same tactic. The "transfer" content (comparing algebraic vs combinatorial proofs) is in the conclusion text, not in the proof work.

**L06** proves `sum m in range 6, (-1)^m * choose 5 m = 0`. The proof is `exact Int.alternating_sum_range_choose_of_ne (by omega)`. This is the same operation as BinomialTheorem L08 -- just instantiated at `n = 5`. Again, the transfer content is in the text, not the proof.

**The problem**: These levels don't test retrieval of a *method* -- they test recall of a *lemma name*. The learner either remembers `Nat.sum_range_choose` or doesn't. There's no proof planning, no multi-step reasoning, no fresh surface form in the proof. The mathematical reflection in the conclusions is valuable, but the Lean proof is trivially a one-liner that doesn't exercise any proof moves.

**Fix**: Either (a) make the statements require the binomial-theorem-specialization method (e.g., prove the row sum by setting `x = y = 1` in `add_pow`, not by citing the precomputed lemma), or (b) merge L05 and L06 into a single "transfer reflection" level with a more interesting proof task.

### P2-01: L01, L02, L03 are structurally uniform

All three are "apply one lemma" levels. L01 uses `rw [Nat.choose_succ_succ]`, L02 uses `rw [show ..., Nat.choose_symm]; omega`, L03 uses `exact Nat.add_choose_eq 4 3 3`. The variety is adequate for retrieval practice, but the pset could benefit from at least one level that combines two of these moves.

## 5. Learner simulation notes

### Attentive novice

**L01-L03**: The novice will need to remember the lemma names (`Nat.choose_succ_succ`, `Nat.choose_symm`, `Nat.add_choose_eq`). The introductions provide enough context. The hidden hints give rescue. **First stuck point**: L02, where the learner needs to rewrite `7` as `10 - 3` before applying symmetry. This is the most technically demanding of the single-lemma levels.

**L04**: The novice needs to recognize `3 = 1 + 2` and think to use `add_pow`. The hidden hint provides rescue. This is a good retrieval challenge.

**L05-L06**: The novice either remembers the lemma or is stuck. The hints give the answer. There's no intermediate step to try. This is weak pset design.

**L07 (Boss)**: The novice reads the introduction, which gives the complete proof plan including tactic names. The "challenge" is typing the steps correctly. The boss is reduced to a transcription exercise. **This is the most serious pedagogical issue in the world.**

### Experienced Lean user

**L01-L03, L05-L06**: All closeable by `rfl` (one tactic). The experienced user will discover this immediately and learn nothing. For L01-L03 this is acceptable (rfl cannot be disabled, P2 severity). For L05-L06, combined with the fact that the intended proofs are also one-liners, the experienced user gets zero value from these levels.

**L04**: Not closeable by `rfl` (universally quantified). The experienced user will likely write `exact add_pow 1 2 n` directly. This is a legitimate one-step retrieval.

**L07**: Not closeable by `rfl`. The experienced user might try `simp` (disabled) or look for a one-liner. The multi-step proof is reasonable. However, the introduction gives the full plan, so even the experienced user can just follow instructions.

## 6. Boss integrity notes (L07)

### Seeded subskills
- `add_pow`: taught in BinomialTheorem L01, practiced in L04, L10. **OK.**
- `push_cast`: taught in BinomialTheorem L02-L03. **OK.**
- `Finset.sum_congr rfl`: taught in FinsetProd L07-L08. **OK.**
- `one_pow`: introduced in BinomialTheorem L10. **OK.**
- `mul_one`: **NOT formally introduced.** Available but undocumented. P2.
- `.symm`: basic Lean. **OK.**

### Closure quality
All subskills have been introduced and practiced. `mul_one` is a gap but minor (NNG4 knowledge).

### Integration quality
**Moderate.** The boss requires: apply binomial theorem -> simplify casts -> simplify `1^(n-m)` terms -> conclude. This is 4 steps, which meets the "5+ integrated moves" guideline approximately. The structure mirrors the BinomialTheorem L10 boss closely (both are "specialize add_pow, simplify, conclude"), differing only in which simplification steps are needed (L10 uses `ring` for `(-1 + 2) = 1`; L07 uses `Finset.sum_congr` for `1^(n-m) * ... = ...`).

### P1-02: Boss introduction spoils the proof plan

The L07 introduction includes:

> 1. Apply `add_pow` with `x = 3, y = 1` to get `h : (3 + 1) ^ n = ...`
> 2. Simplify `(3 + 1)` to `4`
> 3. Simplify `1 ^ (n - m)` to `1` using `one_pow`
> 4. Simplify `... * 1` to `...` using `mul_one`

This is the complete proof strategy with tactic names. For a pset boss, the learner should be retrieving the proof plan themselves. The introduction should state the identity and give the mathematical context (substitution `x = 3, y = 1`), but NOT list the tactic steps. The proof plan section should be removed or converted to a hidden hint.

### Surprise burden
None -- all steps are variants of previously seen patterns. **OK.**

### Can a learner explain why the proof works?
The conclusion provides an excellent explanation. **OK.**

## 7. Pset integrity notes

### Fresh surface form
- L01: Fresh (row 8 vs row 5). **OK.**
- L02: Fresh (pair (10,7) vs general). **OK.**
- L03: Fresh (triple (4,3,3) vs (3,2,2)). **OK.**
- L04: Fresh (substitution (1,2) vs (1,1)). **OK.**
- L05: **Weak.** Same lemma, same proof shape, different number. Not a fresh surface form.
- L06: **Weak.** Same lemma, same proof shape, different number.
- L07: Fresh (substitution (3,1) vs (-1,2)). **OK.**

### Reduced scaffolding
- L01-L06: All hints hidden. **OK.**
- L07: Hints hidden, but introduction provides the complete proof plan. **NOT OK.** (P1-02 above.)

### Real retrieval
- L01-L04: Require retrieving a method and applying it to new values. **OK.**
- L05-L06: Require recalling a lemma name. **Weak** -- this is recognition, not retrieval of a method.
- L07: Would test retrieval if the intro didn't spoil the plan. **Conditional.**

### More than cloning lecture material?
- L01-L04, L07: Yes -- genuinely different instances requiring adaptation. **OK.**
- L05-L06: Essentially clones -- same lemma, same proof structure, only the number changes. **NOT OK.**

## 8. Technical risks

### P2-02: rfl exploit on L01, L02, L03, L05, L06

All five concrete (non-universally-quantified) levels are closeable by `rfl` because `Nat.choose` is a computable function and both sides reduce to the same natural number. Cannot disable `rfl`. Known P2 issue per project standards.

**Mitigation**: Accept as P2. The intended proofs are more educational even if `rfl` works. The issue is more severe for L05/L06 where the intended proofs are also one-liners.

### P2-03: `mul_one` hidden prerequisite in L07 boss

`mul_one` is used in the boss proof but was never introduced via `NewTheorem` anywhere in the course. It's available (not disabled) and is basic NNG4 knowledge. The learner encounters it in a hidden hint that says `rw [one_pow, mul_one]`.

**Fix**: Add `mul_one` to a `NewTheorem` declaration in an earlier world (e.g., BinomialTheorem L10 alongside `one_pow`), or add it in L07 itself.

### Clean: DisabledTactic set

All 7 levels use `DisabledTactic trivial decide native_decide simp aesop simp_all`. This is the standard set. `omega` is correctly left available (needed for L02's `3 ≤ 10` subgoal). **OK.**

### Clean: No missing docs

No `NewTheorem`, `NewTactic`, or `NewDefinition` declarations in the pset (correct for a pset that introduces nothing new). No warnings about missing docs. **OK.**

### Clean: Build

`lake build` succeeds with no errors. Only pre-existing warnings about earlier worlds. **OK.**

## 9. Ranked patch list

| Priority | ID | Issue | Fix |
|----------|-----|-------|-----|
| P1 | 01 | L05/L06 are near-clones: one-liner proofs that just cite a lemma name | Redesign L05 to require proving the row sum via `add_pow 1 1 n` + simplification (the specialization method, not the precomputed lemma). Redesign L06 to require proving the alternating sum via `add_pow 1 (-1) n` + simplification. This makes both levels exercise the specialization proof move instead of lemma recall. |
| P1 | 02 | L07 boss introduction spoils the proof plan | Remove the "Proof plan" section from the introduction. Keep the mathematical context (substitution x=3, y=1 and concrete check). Let the learner retrieve the tactic strategy from prior experience. |
| P2 | 01 | L01-L03 are structurally uniform (all single-lemma) | Optional: combine two moves in one level (e.g., "prove C(10,7) = C(7,2) + C(7,3)" requiring both symmetry and Pascal's rule). Would strengthen pset variety. |
| P2 | 02 | rfl exploit on 5 of 7 levels | Accept as known P2. Cannot disable rfl. |
| P2 | 03 | `mul_one` hidden prerequisite in boss | Add `mul_one` to `NewTheorem` in BinomialTheorem L10 (alongside `one_pow`), or add `NewTheorem mul_one` in L07. |

## 10. What to playtest again after patching

1. **L05 and L06** (after redesign): Verify the new proofs are multi-step, that `rfl` still works (P2 accept), and that the transfer text still makes sense.
2. **L07 boss** (after intro revision): Verify the boss is solvable without the proof plan in the intro. Check that the hidden hints provide adequate rescue.
3. **Full world pass**: Confirm no new build warnings and that the flow from L01 to L07 is coherent after changes.
