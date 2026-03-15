# W22 PermutationWorld — Playtest Audit R1

**World**: PermutationWorld (7 levels)
**Role**: Lecture
**Promise**: "The learner understands `Equiv.Perm (Fin n)` as the group of permutations, and can connect to factorial counting."
**Build**: Passes (`lake build` clean, no PermutationWorld-specific errors).

---

## 1. Overall Verdict

**NEEDS REVISION.** The world is pedagogically well-structured and covers its promise, but has multiple exploitability issues that undermine the intended lessons. L01-L04 are all closable by `rfl` (P2, cannot disable), and L06 is closable by `decide` (but `decide` IS disabled, so fine). The more concerning exploit is `norm_num [Fintype.card_perm, Fintype.card_fin]` on L05 and L07 Part 1 — `norm_num` is not disabled and closes these in one shot, bypassing the intended factorial-unfolding lesson. Additionally, `Fin.forall_fin_succ` + `norm_num` closes L04 entirely, bypassing the `one_def` lesson.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good coverage of M36 across states. Missing: `Equiv.swap_mul_self` is introduced in L04 doc but never used in any level. |
| 2. Granularity fit | 3 | Each level has one dominant lesson. L06 feels slightly disconnected (List.Perm is tangential to the main permutation-as-bijection thread). |
| 3. Proof-move teaching | 3 | Good teach of `rw`-chain pattern for swap evaluation. The composition pattern (L03) is well-structured. Boss integrates counting + Lagrange. |
| 4. Inventory design | 3 | Clean releases. `pow_card_eq_one` introduced at boss is a free theorem (not earned via level), but justified by plan. `Equiv.swap_mul_self` introduced free in L04 but never exercised — inventory clutter risk. |
| 5. Hint design | 3 | Layered hints present. Strategy hint first, code second. Hidden hints available. L07 hints are verbose but functional. |
| 6. Progression | 3 | Demo (L01) -> practice (L02) -> new pattern (L03) -> identity (L04) -> counting (L05) -> misconception (L06) -> boss (L07). Good arc. |
| 7. Mathematical authenticity | 3 | Good connections to symmetric group theory, Lagrange's theorem. Transfer moments in conclusions are solid. |
| 8. Paper-proof transfer | 3 | L07 conclusion explicitly connects Lean proof to paper proof. Good throughout. |
| 9. Technical fit | 2 | `rfl` exploits on L01-L04 (P2, inherent). `norm_num` exploit on L05/L07 (P1, fixable). Missing `TacticDoc` entries generate build info messages (cosmetic but noisy). |

**Average**: 2.89 (below 3.0 threshold for "good")

---

## 3. Coverage Gaps

### Items covered:
| Item | Axis | State | Levels |
|------|------|-------|--------|
| M36: Equiv.Perm definition | MATH | I/S/G | L01 (I), L02-L04 (S), L07 (G) |
| E18: Concrete swap construction | EXAMPLE | I/S | L01 (I), L02 (S) |
| M36: Composition | MATH | S | L03 |
| M36: Identity | MATH | S | L04 |
| M27/M36: Counting (card_perm) | MATH | S/R | L05 (S), L07 (R) |
| C12: List.Perm vs Equiv.Perm | MISCONCEPTION | W | L06 |
| V2: Exhaustion/Lagrange | MOVE | I/G | L07 (I+G) |

### Gaps:
1. **`Equiv.swap_mul_self` is introduced but never exercised.** It appears in L04's `NewTheorem` and `TheoremDoc`, but no level asks the learner to use it. This is inventory clutter — either add a level using it or remove it from L04's `NewTheorem`.
2. **No retrieval of swap evaluation.** L01/L02 introduce swap lemmas, L03 retrieves them inside composition. But after L03, swap evaluation is never needed again (not in L05-L07). The boss does not require swap evaluation at all.
3. **`pow_card_eq_one` is introduced at the boss.** This is the first time the learner sees Lagrange's theorem. The boss introduces AND integrates in the same level — borderline lottery boss for the Lagrange component. The counting component is properly seeded (L05), but the group theory component is brand new.

---

## 4. Granularity Defects

1. **L06 (List.Perm vs Equiv.Perm) is thematically disconnected.** The level is a misconception-clearing exercise about two different uses of "permutation," but its proof (`exact List.Perm.swap 0 1 [2]`) is a one-liner with no connection to the swap-evaluation or composition skills from L01-L04. It feels like an appendix. The concept is valuable but the level does not exercise any skill from this world's repertoire.

2. **Boss introduces `pow_card_eq_one` (Lagrange).** The intended proof pattern for Part 2 is: establish cardinality, rewrite 6 as the cardinality, apply `pow_card_eq_one`. The learner has never seen `pow_card_eq_one` before this level. While the hints walk through it, this is a novel burden at the boss — the boss should integrate, not introduce. **Severity: P1**.

---

## 5. Statement Exploitability

### L01: `rfl` closes it (P2)
`(Equiv.swap (0 : Fin 3) 1) 0 = 1` is definitionally true. `rfl` closes it instantly, bypassing `swap_apply_left`. **Cannot disable `rfl`.** Accept as P2 — the learner who types `rfl` still learns something (that swap evaluation is definitional), and the hints guide toward the intended path.

### L02: `exact ⟨rfl, rfl, rfl⟩` closes it (P2)
All three conjunction parts are definitionally true. Same P2 as L01.

### L03: `rfl` closes it (P2)
The composition `(swap 0 1 * swap 1 2) 0 = 1` is definitionally true. `rfl` bypasses the entire `mul_def` / `trans_apply` / `swap_apply_*` chain. Same P2.

### L04: `intro x; rfl` closes it (P2), `norm_num [Fin.forall_fin_succ]` also closes it (P1)
The identity permutation applied to any element is definitionally equal to that element. `rfl` after `intro` works. Additionally, `norm_num [Fin.forall_fin_succ]` closes it in one shot — this is a P1 exploit since `norm_num` is not disabled.

### L05: `norm_num [Fintype.card_perm, Fintype.card_fin]` closes it (P1)
This one-liner bypasses the intended three-step factorial unfolding. `norm_num` is not disabled. **Fix: add `norm_num` to `DisabledTactic` on L05.**

### L06: `decide` would close it, but `decide` is disabled (OK)
The `List.Perm` statement is decidable, but `decide` is in the disabled set. The learner must use `exact List.Perm.swap 0 1 [2]`. This is fine.

### L07: Part 1 closable by `norm_num [Fintype.card_perm, Fintype.card_fin]` (P1)
Same exploit as L05. Part 2 cannot be closed by `native_decide` (good — universal quantifier over free variable blocks it). But Part 1 can be shortcut. **Fix: add `norm_num` to `DisabledTactic` on L07.**

### L07 Part 2: `have h := ... by norm_num [...]` + `rw [← h]` + `exact pow_card_eq_one`
Even with `norm_num` disabled on the `have` step, the learner still needs to establish the cardinality somehow. If `norm_num` is disabled, the intended factorial-unfolding approach is forced. But currently `norm_num` is available and shortcuts the `have`.

### Summary of exploits:
| Level | Exploit | Severity | Fix |
|-------|---------|----------|-----|
| L01 | `rfl` | P2 | Cannot disable; accept |
| L02 | `⟨rfl, rfl, rfl⟩` | P2 | Cannot disable; accept |
| L03 | `rfl` | P2 | Cannot disable; accept |
| L04 | `rfl` / `norm_num [Fin.forall_fin_succ]` | P2/P1 | Disable `norm_num` on L04 |
| L05 | `norm_num [Fintype.card_perm, Fintype.card_fin]` | P1 | Disable `norm_num` on L05 |
| L06 | None (decide disabled) | OK | - |
| L07 | `norm_num [...]` on Part 1 | P1 | Disable `norm_num` on L07 |

---

## 6. Interactive Proof Quality

### L02: The `refine ⟨?_, ?_, ?_⟩` pattern
The first hint suggests `refine ⟨?_, ?_, ?_⟩`, which requires the learner to type a non-trivial expression. However, the alternative `constructor` (used twice) is also mentioned. The `refine` version is slightly hostile to exploration since the learner must get the syntax right. **P2 — minor.** The `constructor` alternative is available and hinted.

### L03: Four-step rw chain
The proof requires `rw [Equiv.Perm.mul_def]`, `rw [Equiv.trans_apply]`, `rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]`, `rw [Equiv.swap_apply_left]`. Each step is individually typed and produces visible feedback. Good interactive quality.

### L07: The `have` block
The `have h : ... := by ...` block requires the learner to type a multi-line proof term inside a `have`. This is a moderate interactive burden — the learner doesn't get feedback until the entire `have` proof is correct. However, this is a boss level, and the `have` pattern was presumably taught in earlier worlds. **P2 — acceptable for boss.**

---

## 7. Learner Simulation

### Attentive Novice

**First stuck point**: L03, at the `rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]` step. The learner must supply two explicit `by omega` arguments, which is a non-trivial syntax demand. The hint does provide the exact invocation, but the learner may not understand why `by omega` is needed (proof of `0 ≠ 1` and `0 ≠ 2` for `Fin 3`).

**Most likely wrong move**: L07 Part 2 — trying to use `pow_card_eq_one` directly without establishing the cardinality first. The goal says `σ ^ 6 = 1` but `pow_card_eq_one` gives `σ ^ Fintype.card ... = 1`. The mismatch requires the `rw [← h]` step, which is a non-obvious move.

**Hint rescue**: Good. L07's hints explicitly walk through the `have` + `rw [← h]` pattern. The novice should recover.

**Lesson legibility**: Clear for L01-L05. L06's lesson (List.Perm vs Equiv.Perm) is conceptually clear but may feel like an interruption. L07's lesson (Lagrange application) is legible but dense.

### Experienced Lean User

**Avoidable friction**: L01-L03 are trivially closable by `rfl`. An experienced user will immediately type `rfl` and learn nothing. The intended `rw [swap_apply_left]` approach is pedagogically motivated but not forced.

**Alias gaps**: None detected. The intended theorems are the natural ones.

**Inventory clutter**: `Equiv.swap_mul_self` is introduced in L04 but never used. An experienced user might wonder when to use it.

**Needless verbosity**: L05's four `Nat.factorial_succ` rewrites feel mechanical. An experienced user would prefer `norm_num` (which currently works). The intended pedagogical point is seeing factorial unfold, but the repetition is tedious.

---

## 8. Boss Integrity (L07)

### Seeded subskills:
- **Counting** (`card_perm` + `card_fin` + factorial): Seeded in L05. **OK.**
- **`constructor` for conjunction**: Assumed from NNG4 baseline. **OK.**
- **`intro`**: Baseline. **OK.**
- **`have` blocks**: Not taught in this world. Assumed from earlier worlds. **OK if prerequisite worlds teach it.**
- **`rw [← h]` (reverse rewriting)**: Not taught in this world. Assumed from earlier. **OK if prerequisite worlds teach it.**
- **`pow_card_eq_one` (Lagrange)**: **NOT seeded.** First appearance is in the boss itself. This is a new theorem introduced at integration time. **P1 — borderline lottery boss for this component.**

### Closure quality:
Part 1 is well-seeded (L05 does the same computation on `Fin 4` instead of `Fin 3`). Part 2 introduces `pow_card_eq_one` — the learner has never seen it and must trust the hints.

### Integration quality:
The boss does integrate counting (L05) with group theory (new). But the group theory component is not integration — it is introduction. A true integration boss would require the learner to combine skills from WITHIN the world, not introduce an external theorem.

### Surprise burden:
`pow_card_eq_one` is a surprise. The `rw [← h]` pattern is a planning challenge (rewriting a concrete number as a cardinality expression), which is good. But the learner has to learn a new theorem AND apply a planning pattern in the same level.

### Verdict: **P1 — boss partially introduces rather than integrates.**

---

## 9. Course-Role Sanity

- L01: Introduction to `Equiv.Perm` — **correctly cast**.
- L02: Practice with swap evaluation — **correctly cast**.
- L03: New pattern (composition) — **correctly cast** as a coached introduction.
- L04: Identity permutation — **correctly cast**.
- L05: Counting connection — **correctly cast** as new content linking perm to factorial.
- L06: Misconception clearing — **correctly cast**, though placement before the boss feels slightly awkward. The boss doesn't use `List.Perm` at all, so L06 is a standalone conceptual clarification that doesn't feed into L07.
- L07: Boss — **partially miscast**. It is labeled as a boss but introduces `pow_card_eq_one` (Lagrange). A true boss should only integrate previously taught material.

---

## 10. Technical Risks

1. **Build info messages**: "Missing Tactic Documentation" for `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` on every level file. These are cosmetic (the docs exist in earlier worlds and are inherited), but they are noisy.

2. **No `TacticDoc` in this world**: The world introduces no new tactics, so no `TacticDoc` entries are expected. The "Missing" messages are about disabled-tactic docs that exist elsewhere. Harmless.

3. **Translation warnings**: All level titles and introductions generate "No translation found" warnings. This is expected for in-development content.

---

## 11. Ranked Patch List

### P0 (Blocking)
None.

### P1 (High — should fix before shipping)

1. **Add `norm_num` to `DisabledTactic` on L04, L05, and L07.** Currently, `norm_num [Fintype.card_perm, Fintype.card_fin]` closes L05 and L07 Part 1 in one shot, bypassing the factorial-unfolding lesson. On L04, `norm_num [Fin.forall_fin_succ]` bypasses the `one_def` lesson. Fix: change `DisabledTactic` line on L04, L05, and L07 to include `norm_num`:
   ```
   DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
   ```

2. **Seed `pow_card_eq_one` before the boss.** Currently it appears for the first time in L07. Options:
   - (a) Add a pre-boss level (L06.5 or renumber) that introduces `pow_card_eq_one` on a simpler example (e.g., prove `σ ^ 2 = 1` for `Equiv.Perm (Fin 2)` where `card = 2`). Then the boss retrieves it.
   - (b) Accept that the boss introduces Lagrange as a "gift theorem" (free theorem) and explicitly frame Part 2 as "learn and apply a new tool." Document this design choice. Less ideal but viable if the world is meant to be a gateway to group theory, not a mastery world.

3. **Remove `Equiv.swap_mul_self` from L04's `NewTheorem` or add a level using it.** Introducing a theorem that is never exercised is inventory clutter. Either:
   - (a) Add a practice level between L04 and L05 where the learner proves `Equiv.swap 0 1 * Equiv.swap 0 1 = 1` using `swap_mul_self`.
   - (b) Remove `Equiv.swap_mul_self` from `NewTheorem` in L04 (keep the `TheoremDoc` as a reference, just don't introduce it as a "New" item).

### P2 (Medium — acceptable, note for tracking)

4. **L01-L03 closable by `rfl`.** Cannot disable `rfl`. The evaluations are definitionally true for concrete `Fin n` values. Accept as inherent. The hints guide toward the intended approach, and a learner who types `rfl` still passes the level (they just miss the teaching point about the specific lemmas). Consider adding a note in L01's intro: "While `rfl` might work here since these are concrete computations, the lemmas you learn will be essential for abstract permutations."

5. **L06 does not feed into the boss.** The misconception-clearing level about `List.Perm` vs `Equiv.Perm` is pedagogically valuable but is a dead end in terms of skill building. The boss uses neither `List.Perm` nor `List.Perm.swap`. This is acceptable for a misconception level, but the placement right before the boss is awkward — consider swapping L05 and L06, or noting in L06's conclusion that the boss ahead uses only `Equiv.Perm`.

### P3 (Low — minor improvements)

6. **L05 factorial unfolding is mechanical.** Four `Nat.factorial_succ` calls + one `Nat.factorial_zero` feels repetitive. This is the same pattern used in the Factorials world. Consider referencing that this is a retrieval of the factorial-unfolding pattern from the prerequisite world.

7. **L07 Part 2 hint verbosity.** The hint block for Part 2 is quite long (the full `have` proof + `rw` + `exact`). Consider breaking it into two hints: first a strategy hint ("Establish the cardinality as a `have`, then rewrite 6 as the cardinality"), then a hidden implementation hint.

---

## 12. What to Playtest After Patching

1. After adding `norm_num` to `DisabledTactic` on L04/L05/L07: verify the intended proofs still work (they use `rw` chains, not `norm_num`). Verify that `omega` is still available for the `by omega` subproofs in L02/L03 (it should be — `omega` is not disabled).

2. If a pre-boss level for `pow_card_eq_one` is added: verify the boss still integrates properly, and the new level builds.

3. If `Equiv.swap_mul_self` is removed from L04 `NewTheorem`: verify no downstream level references it as a prerequisite.

4. Re-check all levels for `rfl` exploits (P2 accepted) and any new exploits introduced by patches.
