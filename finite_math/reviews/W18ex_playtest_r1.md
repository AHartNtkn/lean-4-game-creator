# W18_ex PascalsTriangle -- Playtest Audit R1

## 1. Overall verdict

**NEEDS REVISION.** The world builds and the pedagogy is coherent at a narrative level, but multiple exploit paths bypass every level, an untaught tactic (`symm`) is required in L05, interactive-hostile proof steps appear in L02 and L05, and the DisabledTactic set is incomplete. The world is not shippable in its current state.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 3 | Covers E17, M28, M30, M31 as planned. T7 transfer is present but weak. |
| Granularity fit | 2 | L01/L03/L06 risk overfine (all boundary-condition rewrites). L05 is overbroad (introduces `symm` + complex rw in one step). |
| Proof-move teaching | 2 | The recursive unfolding pattern is demonstrated but never practiced independently. L05 introduces `symm` without teaching it. |
| Inventory design | 1 | Zero `NewTactic`/`NewTheorem`/`NewDefinition` declarations in the entire world. Build warns about `symm`, `show`, `from` being required but never introduced. |
| Hint design / recoverability | 2 | Hints are consistently layered (strategy visible + direct hidden), but L02 step 3 and L05 step 2 require complex one-liners that are interactive-hostile. No Branch alternatives for common wrong moves. |
| Worked example -> practice -> transfer -> boss | 3 | Good progression from simple rows to row sum to symmetry to transfer. No boss expected (example world). |
| Mathematical authenticity | 3 | Good narrative connecting rows to Pascal's rule. Concrete computations are appropriate. The subset-counting table in L04 conclusion is excellent. |
| Paper-proof transfer | 2 | L06 conclusion has good transfer text, but L06 itself is another Lean computation (boundary conditions on Row 5), not a genuine transfer exercise. The plan says "Draw Pascal's triangle and explain the recursion in words." |
| Technical fit / maintainability | 2 | Builds cleanly but 3 build warnings about missing tactic introductions. No inventory declarations at all. |

**Average: 2.2 -- below the 3.0 threshold. No category at 0 but inventory design is at 1 (red flag).**

## 3. Coverage gaps

### Exploit coverage (P0)

- **`norm_num` exploit**: `norm_num` is not disabled and closes L01, L02, L03, L05, L06 in one shot. Verified by compilation test. This bypasses every intended lesson in 5 of 6 levels.
- **`rfl` exploit**: `rfl` closes L01, L02, L03, L04, L05, L06. Since `Nat.choose` reduces on concrete values, all equalities are definitional. `rfl` cannot be disabled (P2 -- accept and document, per project convention), but `norm_num` can and must be.

### Inventory coverage (P0)

- Zero `NewTactic`, `NewTheorem`, or `NewDefinition` declarations in any level file. The world introduces no inventory items. While this is an example world that reuses prior theory, it should at minimum declare the theorems it expects the learner to use (even if they were `NewTheorem`'d in BinomialCoefficients).

### Hidden prerequisite leaks (P1)

- **`symm` tactic** (L05): Used as a standalone tactic for the first time in the entire course. Never introduced by any `NewTactic` declaration, no `TacticDoc` exists. Build warning confirms: "No world introducing symm, but required by PascalsTriangle."
- **`show ... from rfl` idiom** (L02, L05): The pattern `rw [show (1 : ℕ) = 0 + 1 from rfl, ...]` uses `show` and `from` which are never taught. Build warning confirms: "No world introducing show, but required by PascalsTriangle" and "No world introducing from, but required by PascalsTriangle."
- **`by omega` as inline proof** (L05): The pattern `Nat.choose_symm (by omega : 1 ≤ 4)` uses inline `by` proofs within a `rw` argument, which is a sophisticated Lean idiom not previously taught.

### Transfer coverage (P2)

- L06 is labeled as "Transfer" but is a standard Lean computation (endpoints of Row 5). The plan specifies T7 (S): "Draw Pascal's triangle and explain the recursion in words." The actual level does not ask the learner to articulate understanding in natural language -- it asks for another boundary-condition rewrite.

## 4. Granularity defects

### Overfine levels (P2)

- **L01 (Row 0) and L06 (Row 5 endpoints)**: Both are single `rw [Nat.choose_zero_right]` or `rw [Nat.choose_self]` rewrites. L01 is `choose_zero_right`, L06 is `constructor` + `choose_zero_right` + `choose_self`. L06 is marginally more complex (conjunction splitting) but the proof moves are identical to L01.
- **L01 and L03**: L01 uses `choose_zero_right`, L03 uses `choose_succ_succ` + `choose_zero_right` + `choose_self`. L03 has more steps but the pattern is the same as L02 with different numbers. Together L02 and L03 risk the overfine pattern (same recursion unfolding with different numerals).

### Overbroad level (P1)

- **L05 (Symmetry visible)**: Introduces `symm` tactic (never taught) + `show ... from rfl` idiom (never taught) + `by omega` inline proof (sophisticated) all in a single level. Three new burdens at once.

## 5. Learner simulation

### Attentive novice

**L01**: Smooth. Single `rw [Nat.choose_zero_right]` with clear hints. Can also just type `rfl` and pass (exploit, but novice unlikely to try).

**L02**: First likely stuck point is step 3. After rewriting to `1 + Nat.choose 0 1 = 1`, the hint says to type `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`. This is a 58-character tactic call using idioms (`show ... from rfl`) never explained. A novice will:
- Not understand what `show ... from rfl` means
- Likely mistype the expression
- Get no feedback until the entire rw chain is correct
- Feel frustrated that the hint gave them something they don't understand

**Most likely wrong move at L02 step 3**: Try `rw [Nat.choose_zero_succ]` alone (without the `show` rewrite). This would fail because `Nat.choose_zero_succ` expects the argument in the form `Nat.choose 0 (n + 1)` but the goal has `Nat.choose 0 1`. No hint catches this wrong move.

**L05**: The novice is asked to `symm` first (a tactic they've never seen), then type a complex rw expression. Even with hints, this feels like being given an answer key rather than learning a proof move.

**L06**: Straightforward for a novice who has done L01-L03. No new challenge.

### Experienced Lean user

**L01-L03, L06**: Will immediately try `norm_num` or `rfl` and pass without engaging. The world teaches nothing to an experienced user because there is no inventory gating.

**L04**: Will type `rfl` or `norm_num` (though `norm_num` alone fails on L04, `rfl` works). Alternatively, `native_decide` is disabled, so that path is blocked. But `rfl` closes it.

**L05**: Will immediately try `norm_num` and pass.

**Avoidable friction**: The `show (3 : ℕ) = 4 - 1 from rfl` pattern is unnecessarily verbose. An experienced user would prefer `Nat.choose_symm_diff` or a similar direct lemma. The proof path feels forced.

## 6. Course-role sanity

This world is cast as an **Example** world, which is correct in intent: it concretizes Pascal's triangle by computing specific rows. However:

- **L06 is miscast as Transfer**: It is labeled "Transfer" in the plan but functions as another computation level. A real transfer level should have the learner articulate the recursion in natural language, not prove more equalities.
- **The world as a whole is more "worked example" than "example"**: The proofs are heavily scaffolded with hints giving exact tactic calls. An example world should exercise existing theory with reduced scaffolding, but these levels provide maximum scaffolding on moves that should be retrieval by this point in the course.

## 7. Technical risks

| Risk | Severity | Details |
|------|----------|---------|
| `norm_num` exploit | P0 | Closes L01-L03, L05-L06 in one shot. Must disable on levels where it's not the intended proof tool. |
| `rfl` exploit | P2 | Closes all 6 levels. Cannot disable. Accept per project convention. |
| Missing `NewTactic symm` | P1 | Build warning. L05 uses `symm` but it was never declared. |
| Missing `NewTactic show` | P1 | Build warning. L02 and L05 use `show` but it was never declared. |
| Missing `NewTactic from` | P1 | Build warning. L02 and L05 use `from` but it was never declared. |
| Missing `TacticDoc` entries | P1 | No TacticDoc for any disabled tactics in this world (build info messages about missing docs for trivial, decide, native_decide, simp, aesop, simp_all). |
| No `NewTheorem`/`NewDefinition` | P2 | World declares zero inventory items. Should at minimum reference the theorems used. |
| L02 step 3 interactive-hostile | P1 | Complex one-liner with untaught idiom, no intermediate feedback. |
| L05 step 2 interactive-hostile | P1 | Complex one-liner with inline `by omega`, no intermediate feedback. |

## 8. Ranked patch list

### P0 (Blocking)

1. **Disable `norm_num` on L01, L02, L03, L05, L06.** Keep `norm_num` available only on L04 where it is part of the intended proof. Add `norm_num` to the `DisabledTactic` line on the other 5 levels.

2. **Remove `symm` from L05's intended proof path.** The proof works without `symm`: `rw [show (3 : ℕ) = 4 - 1 from rfl, Nat.choose_symm (by omega : 1 ≤ 4)]` directly on the original goal `Nat.choose 4 1 = Nat.choose 4 3` also works (it rewrites the RHS). Alternatively, restructure to avoid `symm` entirely by proving `Nat.choose 4 3 = Nat.choose 4 1` and using `Eq.symm` at the term level.

### P1 (High)

3. **Break L02 step 3 into smaller interactive steps.** Instead of `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`, split into:
   - Step 3a: `change 1 + Nat.choose 0 (0 + 1) = 1` (or guide the learner to see 1 = 0 + 1)
   - Step 3b: `rw [Nat.choose_zero_succ]`
   Or better: teach the `show ... from rfl` pattern explicitly in a hint before requiring it.

4. **Break L05 step 2 into smaller interactive steps.** Instead of the complex one-liner, split:
   - Step 2a: Rewrite 3 as 4-1 separately
   - Step 2b: Apply `Nat.choose_symm` separately
   - Step 2c: Close the side goal with `omega`

5. **Add `NewTactic` and/or `TacticDoc` declarations.** At minimum:
   - If `symm` is kept: add `NewTactic symm` in L05 and `TacticDoc symm`.
   - Add `TacticDoc` entries for all disabled tactics (or reference them from an earlier world's declaration).

6. **Add a hint/Branch for the common wrong move at L02 step 3.** When a learner tries `rw [Nat.choose_zero_succ]` alone (without the `show` rewrite), they should get a helpful error hint explaining why it didn't match and what they need to do first.

### P2 (Medium)

7. **Rethink L06 as genuine transfer.** The plan says "Draw Pascal's triangle and explain the recursion in words" but the level is another computation. Consider making L06 a verbal transfer exercise: have the conclusion text do the heavy lifting (as it somewhat does), but make the Lean task something that genuinely tests understanding of the recursive structure, not just another boundary-condition rewrite.

8. **Consider merging L01 into L02 or L06.** L01 (Row 0: `choose_zero_right`) is a single-rewrite level that adds minimal value on its own. It could be the first step of L02 (show both Row 0 and Row 1) or could be absorbed. Similarly, L06 (Row 5 endpoints) does the same moves as L01.

9. **Add `NewTheorem` references.** Even though these theorems were introduced in BinomialCoefficients, the world should declare which theorems it expects the learner to use, so the inventory panel is useful.

10. **Document the `rfl` exploit.** Add a note in the world file or intro that `rfl` can close concrete `Nat.choose` equalities because the function reduces on numerals. This is accepted as P2 per project convention.

## 9. What to playtest again after patching

- **L01-L03**: After adding `norm_num` to DisabledTactic, verify that `norm_num` is actually blocked and the intended proof paths still work.
- **L02 step 3**: After breaking into smaller steps, simulate a novice who doesn't know `show ... from rfl` -- does the new hint sequence guide them?
- **L05**: After removing `symm` from the proof path and breaking into steps, does the level still teach `choose_symm` concretization? Are the hints clear?
- **L04**: Verify that `norm_num` still works for the `2^4 = 16` step (it should, since we only disable on other levels).
- **L06**: If redesigned, verify the new task matches the transfer role.
- **All levels**: Verify the `rfl` exploit is accepted/documented and no new exploits were introduced.
