# W15 FinsetProd -- Playtest Audit (Round 1)

## 1. Overall verdict

**Not yet passing.** The world builds cleanly and has a logical pedagogical arc, but it has multiple exploit vectors that bypass dominant lessons, a boss that fails to integrate the world's namesake (`Finset.prod`), and missing inventory declarations. These issues must be fixed before the world is considered complete.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `prod_mul_distrib` and `prod_congr` documented but never exercised. Boss uses only sum-side lemmas. Product material (L01-L04) has no integration after L04. |
| 2. Granularity fit | 3 | Each level has a clear dominant lesson. L05-L06 are single-step but acceptable as I-stage. L04 overloads (`ring` + induction + `prod_range_succ`). |
| 3. Proof-move teaching | 3 | Good explanation of rewrite direction (L06), congr pattern (L07), induction template (L04). Weakened by L07's `ring` bypass. |
| 4. Inventory design | 1 | No `NewTactic ring` anywhere in this world. No `NewTheorem` on any level except for the specific lemmas. `ring` is the world's most important new tactic and is invisible in inventory. |
| 5. Hint design / recoverability | 3 | Hints are properly layered (strategy visible, code hidden). L08's `have` hint is complex but necessary. No hint for common wrong moves (e.g., trying `ring` alone on L07). |
| 6. Worked example -> practice -> transfer -> boss | 2 | L01-L03 introduce, L04 practices, but the boss does not integrate the product half. No transfer moment for products. |
| 7. Mathematical authenticity | 3 | Good sum/product comparison tables. Transfer moment in L08 conclusion connects to paper proof. Missing concrete numerical product computation. |
| 8. Paper-proof transfer | 3 | L08's transfer paragraph is well-written. L04's conclusion connects multiplicative induction to additive. |
| 9. Technical fit / maintainability | 3 | Builds cleanly. DisabledTactic present on all 8 levels. Info-level warnings about TacticDoc are cosmetic (declared upstream). |

**Average: 2.6 (below the 3.0 threshold for "good")**

## 3. Coverage gaps

| Item | Axis | Status | Issue |
|------|------|--------|-------|
| `Finset.prod` | MATH | I (L01) | Introduced but never integrated in boss. |
| `Finset.prod_mul_distrib` | MATH | I (L05 doc only) | Documented in L05 conclusion/TheoremDoc, never exercised. |
| `Finset.prod_congr` | MATH | I (L07 doc only) | Documented in L07 conclusion/TheoremDoc, never exercised. |
| `ring` tactic | LEAN | I (L04) | Used inside induction, not isolated. No `NewTactic` or `TacticDoc` in this world. |
| Sum/product API duality | TRANSFER | Mentioned (L01 table) | Never explicitly named as a transferable prediction strategy. |
| Concrete product computation | EXAMPLE | Missing | No level fully evaluates a product to a number (e.g., 4! = 24). |

## 4. Granularity defects

### 4a. L04 is overbroad (P1)
L04's title is "Using ring with products" and the plan marks it as the introduction of `ring` (L7 (I)). But the level requires `induction`, `rfl`, `prod_range_succ`, the inductive hypothesis, AND `ring`. A learner stuck on this level cannot tell whether they are confused about induction or about `ring`. The first contact with `ring` should isolate it.

**Fix**: Insert a new level before L04 that uses `ring` alone on a simple algebraic identity (e.g., `a * (b + c) = a * b + a * c`). Renumber subsequent levels.

### 4b. L05 and L06 are single-step (P3 -- acceptable)
Each is a single `rw` call. Acceptable for I-stage introduction, but there is no follow-up exercise that requires the reverse direction or a two-step combination. The boss partially addresses this for L06 (`← mul_sum`) but not for L05.

## 5. Learner simulation

### Attentive novice

**First stuck point**: L04 (induction proof). The novice has used `rw` in L01-L03 and is now suddenly asked to do an induction proof with multiple cases. If they have not done induction recently, they will struggle with the `induction n with` syntax and the `| zero =>` / `| succ n ih =>` case split. The hint "Start with `induction n with`" helps, but the jump in complexity from L03 (single `rw`) to L04 (5-step induction) is steep.

**Most likely wrong move on L07**: Typing `ring` (which closes the goal immediately). The novice who learned `ring` in L04 may try it reflexively. The level passes, but they never learn `sum_congr`. The world's dominant lesson for L07 is completely bypassed.

**Most likely wrong move on L08**: Trying `rw [Finset.sum_add_distrib]` first (before `sum_congr`). This would work on `∑ (3 * i + i * i)` but leave `i * i` vs `i ^ 2` unresolved later. The hint correctly guides congr-first, but a learner who skips hints will get stuck.

**Hint rescue**: Generally good. The hidden hints give exact code. L08's `have` construction is complex (multi-line) and may be hard to type correctly in the game interface, but the hidden hint shows the full code.

### Experienced Lean user

**`ring` one-liner on L07**: An experienced user will immediately see that `ring` closes the whole goal and type it. They learn nothing about `sum_congr`. This is the most serious exploit.

**`norm_num` on L01-L03**: An experienced user can close L01 (`norm_num`), L02 (`rfl` or `norm_num`), and L03 (`rfl` or `norm_num`). All concrete numeric equalities. These bypass the intended API lemmas entirely.

**`rfl` on L01-L03**: Even more minimal. L01, L02, L03 are all definitionally true, so `rfl` closes them. Cannot disable `rfl`. This is a P2 issue (inherent to the statement design with concrete values).

**Avoidable friction**: None significant. The levels are clean and well-scoped.

**Inventory clutter**: No `NewTactic` or `NewTheorem` clutter -- in fact the opposite problem: not enough is declared.

## 6. Boss integrity (L08)

### Boss subskill seeding

| Subskill | Where seeded | Status |
|----------|-------------|--------|
| `Finset.sum_congr rfl` | L07 | Seeded |
| `ring` (pointwise) | L04 | Seeded (but overloaded with induction) |
| `Finset.sum_add_distrib` | L05 | Seeded |
| `← Finset.mul_sum` | L06 | Seeded (forward direction only) |
| `have` with a universally-quantified statement | Not explicitly | **Partial**: `have` is NNG4 baseline but `have h : ∀ x ∈ s, ... := by intro x _; ring` is a new pattern. L07 uses `intro x _` but not inside a `have`. |

### Boss integration quality

**Weak.** The boss integrates three sum-manipulation lemmas (L05, L06, L07) in sequence. Each step is a direct application of one lemma. The only planning challenge is recognizing that congr must come first to normalize `i * i` to `i ^ 2`. This is a legitimate integration demand, but it is modest.

**Critical gap**: The boss uses NO product-side lemmas. The world is titled "Finset.prod and algebraic manipulation" and the plan row for L08 explicitly says "requires both sum and prod manipulations." The implementation delivers only sums. This means L01-L04 (the product half) has zero integration. The boss is a sum-manipulation boss, not a FinsetProd boss.

### Novel `have` pattern in boss (P1)

The boss hint suggests `have h : ∀ x ∈ Finset.range n, ... := by intro x _; ring` followed by `rw [Finset.sum_congr rfl h]`. This is a new pattern: constructing a universally-quantified proof in a `have` and then passing it as an argument. This was NOT practiced in any prior level. L07 used `apply Finset.sum_congr rfl` and then `intro x _; ring` as separate tactic steps, but the boss requires combining these into a single `have`. This is a hidden prerequisite.

**Fix**: Either (a) add a coaching level before the boss that demonstrates the `have h : ... := by ...; rw [..., h]` pattern, or (b) restructure the boss proof to use `apply Finset.sum_congr rfl` then `intro x _; ring` (as in L07) before continuing with `rw [sum_add_distrib]`.

## 7. Technical risks

### 7a. `norm_num` bypasses L01, L02, L03 (P1)

`norm_num` is NOT in the DisabledTactic list. It closes all three concrete-value levels:
- L01: `∏ x ∈ ({3} : Finset Nat), x = 3` -- `norm_num` closes it
- L02: `∏ x ∈ (∅ : Finset Nat), (x + 1) = 1` -- `norm_num` closes it
- L03: `∏ i ∈ Finset.range 4, (i + 1) = (∏ i ∈ Finset.range 3, (i + 1)) * 4` -- `norm_num` closes it

**Fix**: Add `norm_num` to DisabledTactic for L01, L02, L03 (and possibly L04 where `simp` already closes it but is disabled).

### 7b. `rfl` bypasses L01, L02, L03 (P2)

`rfl` closes L01 (prod_singleton is definitional), L02 (prod_empty is definitional), and L03 (concrete range products evaluate definitionally). Cannot disable `rfl`. Accept as P2 -- inherent to using concrete numeric statements. Could be partially mitigated by using less trivially-decidable statements, but this would conflict with the pedagogical goal of starting with simple concrete examples.

### 7c. `ring` bypasses L07 (P1)

`ring` as a one-liner closes `∑ i ∈ range n, (i + i) = ∑ i ∈ range n, (2 * i)`. The dominant lesson (sum_congr) is completely bypassed. `ring` cannot be disabled because the intended proof uses it in the pointwise step.

**Fix**: Change the L07 statement so that `ring` alone cannot close it. Options:
1. Make the two sides range over different (but provably equal) sets: `∑ i ∈ s, (i + i) = ∑ i ∈ s, (2 * i)` where `s` is a hypothesis -- `ring` won't close this because it doesn't know about finsets.
2. Use a function that `ring` doesn't handle (e.g., involving `Nat.succ` or a conditional).
3. Make the statement require proving equality of sums over sets that need `rfl` as the first argument to `sum_congr` -- i.e., the two finsets are syntactically different but provably equal, forcing `sum_congr` with a non-`rfl` first argument.

### 7d. `simp` closes L04 but is already disabled (OK)

`simp` can close `∏ i ∈ range n, 2 = 2 ^ n` but `simp` is in DisabledTactic. No action needed.

### 7e. Missing `NewTactic ring` (P1)

`ring` is the most important new tactic in this world. It is used in L04, L07, L08, but never declared with `NewTactic ring`. The `TacticDoc ring` exists upstream (in FinsetExploration L04), but if this world is meant to formally introduce `ring` for big-operator work (plan: L7 (I)), it should have its own `NewTactic` declaration.

**Fix**: Add `NewTactic ring` to the level that introduces `ring` (L04, or the new isolated `ring` level if one is added per enrichment suggestion 3).

### 7f. Build info warnings about TacticDoc (P3 -- cosmetic)

Build emits info-level messages about missing TacticDoc for `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` at L08. These are declared upstream in MultisetHierarchy and ListBasics. The warnings are cosmetic ("Using existing docstring") and do not affect functionality.

## 8. Ranked patch list

| # | Severity | Issue | Fix |
|---|----------|-------|-----|
| 1 | P0 | Boss (L08) does not use any product-side lemma, contradicting world promise and plan. | Redesign boss to require both sum and product manipulation. Fold `prod_congr` or `prod_mul_distrib` into the boss statement. |
| 2 | P1 | `norm_num` bypasses L01, L02, L03. | Add `norm_num` to DisabledTactic for L01, L02, L03. |
| 3 | P1 | `ring` bypasses L07 (dominant lesson: `sum_congr`). | Redesign L07 statement so `ring` alone cannot close it. |
| 4 | P1 | Missing `NewTactic ring`. | Add `NewTactic ring` (+ verify `TacticDoc ring` exists upstream or add one). |
| 5 | P1 | L04 overloads `ring` introduction with induction. | Insert an isolated `ring` level before L04. |
| 6 | P1 | Boss uses novel `have h : ∀ x ∈ s, ... := by ...` pattern never practiced. | Either add a coaching level or restructure boss proof to use `apply sum_congr rfl; intro x _; ring` as in L07. |
| 7 | P2 | `rfl` bypasses L01, L02, L03 (definitional equality on concrete values). | Accept as P2. Inherent to concrete-value statements. Cannot disable `rfl`. |
| 8 | P2 | `prod_mul_distrib` documented but never exercised. | Add a practice level or fold into redesigned boss. |
| 9 | P2 | `prod_congr` documented but never exercised. | Add a practice level or fold into redesigned boss. |
| 10 | P2 | No concrete numerical product computation (e.g., 4! = 24). | Add a level after L03 that fully evaluates a product. |
| 11 | P2 | Sum/product API duality never explicitly named as transferable strategy. | Add a paragraph in L05 or L07 conclusion naming the pattern. |
| 12 | P3 | L02 title "prod_empty and prod_singleton" misleading -- only exercises prod_empty. | Rename to "The empty product" or similar. |

## 9. What to playtest again after patching

After implementing the patches above, the following need re-audit:

1. **Redesigned boss (L08)**: Verify it integrates both sum and product manipulation, that the new statement is not exploitable, that hints cover all steps, and that no hidden prerequisites remain.
2. **New isolated `ring` level**: Verify it properly isolates `ring`, has appropriate hints, and is not exploitable.
3. **L07 with revised statement**: Verify `ring` no longer closes it as a one-liner, that the intended proof path still works, and that the new statement is pedagogically clear.
4. **L01-L03 with `norm_num` disabled**: Verify no other exploit vectors opened up.
5. **Any new practice levels for `prod_mul_distrib` or `prod_congr`**: Full audit of hint coverage and exploitability.
6. **Full world `lake build`**: Verify clean compilation after all changes.
