# W21 FinsuppWorld — Playtest Audit R1

## 1. Overall verdict

**BLOCKED — requires patching before ship.**

The world compiles and the 8-level ladder is structurally sound, but a systemic `norm_num` exploit renders 6 of 8 levels bypassable without engaging the intended lesson. The boss is a gauntlet (three independent sub-proofs concatenated with no interaction). `if_pos` and `if_neg` are used throughout but never formally introduced or documented.

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 2 | `if_pos`/`if_neg` never introduced with `NewTheorem`/`TheoremDoc`; used in every level |
| Granularity fit | 3 | Each level has a clear dominant lesson; L01 and L02 are close in move but justified |
| Proof-move teaching | 2 | The `single_apply` → `if_pos`/`if_neg` pattern is well-taught, but `norm_num` bypasses it entirely |
| Inventory design | 2 | Missing `NewTheorem` for `if_pos`/`if_neg`; no `TheoremDoc` for them |
| Hint design / recoverability | 3 | Hints are layered (strategy visible, code hidden) and well-targeted |
| Worked example → practice → boss | 2 | Boss is a gauntlet concatenation, not genuine integration |
| Mathematical authenticity | 3 | Good motivation (polynomials, free modules, formal sums); transfer moment in boss conclusion |
| Paper-proof transfer | 3 | Conclusions consistently translate to plain language |
| Technical fit / maintainability | 3 | Compiles; clean file structure; DisabledTactic present but incomplete |

**Average: 2.56 — below the 3.0 threshold. No category at 0 or 1, but four categories at 2.**

## 3. Coverage gaps

### P0: `norm_num` exploit (systemic)

`norm_num` is not in `DisabledTactic` for any level. It closes:

| Level | Goal | `norm_num` closes? |
|-------|------|-------------------|
| L01 | `(single 3 5) 3 = 5` | **YES** — full bypass |
| L02 | both conjuncts | **YES** — `constructor <;> norm_num` |
| L03 | support = {3} | No |
| L04 | `(single 1 3 + single 2 5) 1 = 3` | **YES** — full bypass |
| L05 | value = 0 ∧ ∉ support | **YES** — single `norm_num` closes both |
| L06 | `sum ... = 5` | **YES** — full bypass |
| L07 | `sum ... = 3 + 5` | No (RHS is `3 + 5` not `8`) |
| L08 | triple conjunction | **PARTIAL** — parts 1 and 3 bypass; part 2 (support) does not |

Six of eight levels are fully or partially bypassable. The intended lessons (single_apply, if_pos/if_neg, add_apply, sum_single_index) are never forced.

**Fix**: Add `norm_num` to `DisabledTactic` on every level. The internal `(by omega)` and `(by ring)` arguments in the proof scripts are in sub-proofs and should still work (they are inside `by` blocks within arguments, not top-level tactics). Verify after patching.

### P1: `if_pos`/`if_neg` never formally introduced

These theorems are used starting from L01 but have no `NewTheorem` declaration and no `TheoremDoc`. The build log confirms: "No world introducing if_neg, but required by FinsuppWorld" and "No world introducing if_pos, but required by FinsuppWorld."

The learner sees `if_pos` and `if_neg` in hints but has no inventory entry explaining what they are, what their types are, or when to use them.

**Fix**: Add `TheoremDoc` entries for `if_pos` and `if_neg` in L01 (where they are first used), and add `NewTheorem if_pos if_neg` to L01's inventory block (alongside `Finsupp.single_apply`).

### P2: No `NewTactic` declarations in any level

No tactics are introduced in this world. This is acceptable IF all tactics used (`constructor`, `intro`, `rw`, `exact`, `refine`, `omega`, `ring`) are already available from prerequisite worlds — and they are. However, the world uses `ring` (in L08's `by ring`) which was introduced in FinsetExploration. Confirm FinsuppWorld's dependency chain includes FinsetExploration (it does, via BigOpAdvanced).

## 4. Granularity defects

### P1: Boss is a gauntlet (Failure Taxonomy #8b)

L08 is a triple conjunction where each part is solved independently by replaying a prior level's proof. The three parts are:

1. Evaluation: replay L01/L02 technique (single_apply + if_pos)
2. Support: replay L03 technique (support_single_ne_zero)
3. Sum: replay L06 technique (sum_single_index) with trivial `ring` instead of `rfl`

There is no interaction between the parts. No planning challenge. No moment where the learner must see the whole structure. The proof is longer but no harder to *plan* than any individual level.

**Fix**: Redesign the boss so the parts interact. Options:
- A goal where the learner must first compute the support, then use the support characterization to set up a sum, then evaluate the sum — with the output of one step feeding into the next.
- A proof about `f + g` that requires combining `add_apply` with `support` reasoning and `sum_add_index'`, forcing the learner to sequence these tools with genuine dependency.
- A goal like: "Given `f = single 1 3 + single 2 5`, prove `f.sum (fun a m => a * m) = 13`" — this requires the learner to use `sum_add_index'` to split, then `sum_single_index` on each piece, then arithmetic. The steps genuinely depend on each other.

### P2: L04 multi-rewrite chain is interactive-hostile

The hidden hint for L04 shows:
```
rw [Finsupp.single_apply, if_pos rfl,
    Finsupp.single_apply, if_neg (by omega)]
```

This is a 4-item rewrite chain. The learner must type all four correctly before seeing any feedback. Per operational lessons doc, multi-rewrite chains should be broken into individual steps with hints after each.

The model proof does this in one line. Better: break into individual rewrites so the learner can explore incrementally.

**Fix**: Restructure L04's model proof to use individual `rw` steps, with a hint after each.

### P2: L07 complex lambda side-conditions

L07 requires typing:
```
rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
```

This is a single tactic with two anonymous function arguments. A novice must get both lambdas exactly right before seeing any feedback. The hint explains the side conditions well, but the interactive experience is poor.

**Fix**: Consider breaking into `have h1 : ...` and `have h2 : ...` for the two side conditions, then `rw [Finsupp.sum_add_index' h1 h2]`. This gives the learner three incremental steps instead of one monolithic one.

## 5. Learner simulation

### Attentive novice

**First stuck point**: L01, after `rw [Finsupp.single_apply]`. The goal becomes `(if 3 = 3 then 5 else 0) = 5`. The novice may not know `if_pos` exists. The hint says "use `rw [if_pos rfl]`" which is good, but the novice has never seen `if_pos` before (no inventory entry). They will follow the hint mechanically without understanding *why* `if_pos` works.

**Most likely wrong move**: In L02, trying `rfl` after `rw [Finsupp.single_apply]` on the second branch (where the goal has `if 1 = 2`). The hint rescues well by explicitly explaining the `if_neg` pattern.

**Hint rescue**: Generally good. Strategy hints are visible; code is hidden. But the hint layering in L05 is especially good — it walks through the contradiction argument step by step.

**Legibility of lesson**: The dominant lesson (evaluate Finsupp via single_apply + if_pos/if_neg) is clear and well-reinforced. But L07's lesson (sum_add_index') is obscured by the complexity of the lambda side-conditions.

### Experienced Lean user

**Avoidable friction**: The experienced user will immediately try `norm_num` and close 6 of 8 levels without engaging. This is the core exploit.

**Alias gaps**: None identified. The Finsupp API names are standard Mathlib names.

**Inventory clutter**: Minimal — the world introduces 6 theorems and 3 definitions across 8 levels, all focused on Finsupp.

**Forced verbosity**: L04's 4-item rewrite chain and L07's lambda side-conditions are unnecessarily verbose. An experienced user would prefer `simp` (which is correctly disabled) but finds no cleaner alternative available.

## 6. Boss integrity notes

### L08 Boss: FAIL — gauntlet

- **Seeded subskills**: Yes — all three parts (evaluation, support, sum) are taught in L01-L06.
- **Closure quality**: Good — each subskill has introduction and practice.
- **Integration quality**: FAIL — no integration. Three independent sub-proofs in a conjunction. No step depends on a prior step's output.
- **Surprise burden**: Low — the only "twist" is `by ring` instead of `rfl` in part 3, which is trivial.
- **Can the learner explain in words why the proof works?** "I proved three separate things and packaged them with `constructor`." This is not integration — it is packaging.

## 7. Technical risks

1. **Build warnings**: "No world introducing `if_neg`/`if_pos`, but required by FinsuppWorld." These are real missing inventory items.
2. **`by omega` inside DisabledTactic**: If `omega` is added to DisabledTactic, the `(by omega)` arguments inside proof scripts may break. Currently `omega` is NOT disabled and should not be. But verify that adding `norm_num` to DisabledTactic does not break the internal `(by ring)` in L08's proof.
3. **No `TacticDoc` for any disabled tactic**: The DisabledTactic line lists `trivial decide native_decide simp aesop simp_all`. If any of these lack `TacticDoc` entries in earlier worlds, there will be build warnings. The build log does show "Add `TacticDoc simp_all` somewhere above this statement" — this needs fixing.

## 8. Ranked patch list

| Priority | Level(s) | Issue | Fix |
|----------|----------|-------|-----|
| **P0** | ALL | `norm_num` exploit bypasses 6/8 levels | Add `norm_num` to `DisabledTactic` on all 8 levels |
| **P1** | L01 | `if_pos`/`if_neg` never formally introduced | Add `NewTheorem if_pos if_neg` and `TheoremDoc` entries to L01 |
| **P1** | L08 | Boss is a gauntlet (no integration) | Redesign boss to require genuine interaction between evaluation, support, and sum |
| **P2** | L04 | Multi-rewrite chain is interactive-hostile | Break 4-item `rw` into individual steps with per-step hints |
| **P2** | L07 | Complex lambda side-conditions in single tactic | Break into `have` steps for side-conditions |
| **P2** | Pre-L01 | Missing `TacticDoc simp_all` | Add `TacticDoc simp_all` in an earlier world or at top of L01 |

## 9. What to playtest again after patching

1. **All levels**: Verify `norm_num` is actually blocked after adding to DisabledTactic. Verify `(by omega)` and `(by ring)` inside proof arguments still work.
2. **L01**: Verify `if_pos`/`if_neg` appear in learner inventory after adding `NewTheorem`.
3. **L08 (redesigned boss)**: Full playtest of the new boss for integration quality, seeding completeness, and hint coverage.
4. **L04 and L07**: Verify the broken-up proof steps work interactively and hints fire correctly at each step.
