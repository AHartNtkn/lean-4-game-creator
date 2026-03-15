# W19 BinomialTheorem — Playtest Audit R1

**World**: BinomialTheorem (W19, Lecture, 10 levels)
**Auditor**: Playtest auditor R1
**Build**: PASS (lake build succeeds, 0 errors)
**Verdict**: FAIL — requires major revision before R2

---

## 1. Overall Verdict

The world compiles and the DisabledTactic baseline is present on every level. However, the world has **critical structural problems** that make it pedagogically ineffective:

1. **8 of 10 levels are one-liner `exact` proofs** — the learner types a single library lemma with arguments and is done. There is no proof-move teaching, no discovery, and no interactive exploration.
2. **The plan called for an inductive proof of the binomial theorem (L03-L06)** but the implementation completely skipped this, replacing it with more one-liner library calls. The proof-move layer for the binomial theorem — the entire reason this is a separate world from BinomialCoefficients — is absent.
3. **`push_cast` is introduced (L02) but never used again** — zero supported practice, zero retrieval, zero integration. The boss doesn't use it. No subsequent level uses it.
4. **`norm_num` exploit on L02** bypasses the dominant lesson (`push_cast`) entirely.
5. **The boss is a gauntlet** that could be collapsed to fewer steps via `norm_num at h`, and doesn't integrate `push_cast` or Vandermonde despite the world teaching both.

The world reads like a "theorem trivia tour" — it introduces library lemmas and immediately proves them by `exact`. The quality rubric category "Proof-move teaching" scores 0-1 for L01, L03-L09.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 1 | `push_cast` has no closure (I only). Plan items M29(I/S), M28(R) skipped. |
| Granularity fit | 1 | 8 one-liner levels teach no reusable move. Many are overfine (L03 vs L09 are near-clones). |
| Proof-move teaching | 1 | Only L02 (push_cast+ring) and L10 (boss) involve multiple tactic steps. Everything else is `exact`. |
| Inventory design | 2 | Items introduced at reasonable times. But `push_cast` introduced and orphaned. |
| Hint design & recoverability | 2 | Hints are layered (strategy + hidden exact), but on one-liner levels hints ARE the entire proof. No rescue needed because there's nothing to get stuck on. |
| Progression (example->practice->boss) | 1 | No progression — it's 8 library calls then a boss. No practice, no retrieval, no fading. |
| Mathematical authenticity | 2 | Intros and conclusions explain the math well. But learner never actually *does* math — just calls lemmas. |
| Paper-proof transfer | 2 | L09 is a transfer level. Conclusions connect to paper proofs. But proofs don't model paper-proof structure because they're all one-liners. |
| Technical fit | 3 | Compiles, DisabledTactic present everywhere, docs provided for new items. |

**Average: 1.67 — below 3 threshold, multiple categories below 2. FAIL.**

---

## 3. Coverage Gaps

### P0: Missing planned content (plan deviation)

The plan (PLAN.md lines 697-700) called for:
- **L03**: Binomial theorem base case (prove for n=0) — M29 (I)
- **L04**: Inductive step part 1 (expand (a+b)*(a+b)^n) — M29 (S)
- **L05**: Inductive step part 2 (use Pascal's rule to recombine) — M29 (S), M28 (R)
- **L06**: Full assembly — M29 (S)

None of these exist. Instead:
- L03 = `exact add_pow x y n` (one-liner in Z)
- L04 = `exact add_pow 1 1 n` (row sum specialization)
- L05 = `exact Nat.sum_range_choose n` (row sum identity)
- L06 = `exact Nat.add_choose_eq m n k` (Vandermonde)

**Impact**: The proof-move content for the binomial theorem (induction, expansion, Pascal's rule as ingredient) is completely absent. M28 (Pascal's rule) was supposed to get retrieval (R) status here — it does not.

### P0: `push_cast` has no closure

`push_cast` is introduced in L02 and never used again. No supported practice, no retrieval, no integration in the boss. This is a textbook case of coverage state I-only.

### P1: No proof involving `push_cast` + `add_pow` together

The whole point of teaching `push_cast` in a binomial theorem world is that working with `add_pow` in non-ℕ rings produces casts. But no level requires the learner to apply `add_pow` AND then simplify the resulting casts with `push_cast`. L03 works in Z but just calls `exact add_pow`; L08 uses a library lemma for the alternating sum.

### P1: L03 and L09 are near-clones

L03: `exact add_pow x y n` (in Z)
L09: `exact add_pow a b n` (in N, labeled "transfer")

Both are identical in proof shape. The "transfer" label on L09 is hollow — it transfers nothing because the same library call works in both cases.

### P2: Vandermonde identity has no multi-step proof

L06 introduces Vandermonde as `exact Nat.add_choose_eq m n k`. L07 applies it concretely as `exact Nat.add_choose_eq 2 3 2`. Neither involves a multi-step proof. The combinatorial meaning is only in the conclusion text.

---

## 4. Granularity Defects

### P0: Overfine — 8 one-liner levels

Levels L01, L03, L04, L05, L06, L07, L08, L09 are all single-tactic `exact` levels. Each can be solved in one keypress. They differ only in which library lemma is called. By the granularity test: "it teaches no reusable move" — calling `exact some_lemma` is not a reusable proof skill.

These 8 levels should either:
1. Be restructured to involve actual multi-step proofs (per the plan), or
2. Be absorbed into fewer levels with more substance.

### P1: The world has no center of gravity

A lecture world should teach a proof pattern or theorem family through progressive difficulty. This world's center of gravity is "know library lemma names" — which is an inventory task, not a proof-move task. The plan's center of gravity (building up the inductive proof of the binomial theorem) is absent.

### Gauntlet boss (P1)

The boss (L10) applies `add_pow`, then simplifies with `rw`. The 4 steps are:
1. `have h := add_pow (-1 : ℤ) 2 n`
2. `have h2 : (-1 : ℤ) + 2 = 1 := by ring` + `rw [h2] at h`
3. `rw [one_pow] at h`
4. `exact h.symm`

This is the ONLY multi-step proof in the world besides L02. While it integrates `add_pow` and `rw`, it does NOT integrate:
- `push_cast` (taught in this world)
- Vandermonde (taught in this world)
- Pascal's rule (supposed to be retrieved per the plan)

The boss tests "specialize and simplify" but not the world's full repertoire.

---

## 5. Learner Simulation

### Attentive novice

**First stuck point**: None. Every level from L01-L09 has the exact answer in the hint. The novice reads the hint, types `exact add_pow 2 3 2`, and moves on. The boss (L10) is the first real challenge, but even there the hints give exact code.

**Most likely wrong move**: On L10, the novice might try `exact add_pow (-1) 2 n` without `have`, getting a type mismatch. The hint rescues this.

**Hint rescue quality**: Adequate for the boss (layered, step-by-step). On one-liner levels, hints are the entire proof — there is no space between "stuck" and "solved."

**Legibility of lesson**: The novice learns that library lemmas exist for these identities. They do NOT learn how to prove the binomial theorem, how to use `push_cast` in practice, or how to set up an inductive argument. The stated world promise ("can prove the binomial theorem") is not fulfilled — the learner can *cite* the binomial theorem, not prove it.

### Experienced Lean user

**Avoidable friction**: Low. The one-liners are fast.

**Alias gaps**: None identified.

**Inventory clutter**: `Finset.antidiagonal` is introduced but only used in L06-L07, both one-liners.

**Needless forced verbosity**: None — if anything, levels are too terse.

**Exploit**: `norm_num` closes L02 entirely, bypassing `push_cast`. An experienced user will immediately reach for `norm_num` on a cast equation.

---

## 6. Boss Integrity Notes

### L10 Boss

- **Seeded subskills**: `add_pow` (L01) — YES. `rw ... at h` — assumed from prior worlds. `one_pow` — NEW (introduced at the boss). `ring` — assumed from prior worlds. `have` — assumed from prior worlds.
- **Missing seeding**: `one_pow` is introduced AT the boss (NewTheorem on L10). The boss is the first time the learner sees this lemma. This is a **lottery boss defect** — using an untaught lemma as a key step.
- **Closure quality**: POOR. `push_cast` and Vandermonde, both taught in this world, are not integrated.
- **Integration quality**: LOW. The boss only combines `add_pow` + `rw` + `ring` + `exact .symm`. Two of these (`rw`, `ring`) are from much earlier worlds. The boss barely integrates this world's content.
- **Surprise burden**: `one_pow` is a surprise (new lemma at the boss).
- **Explain in words**: Yes, the conclusion explains the specialization strategy clearly. This is a bright spot.

---

## 7. Technical Risks

### P1: `norm_num` exploit on L02

`norm_num` alone closes L02 (`push_cast` introduction level), completely bypassing the dominant lesson. `norm_num` is not in the DisabledTactic list. **Fix**: Add `norm_num` to DisabledTactic on L02.

### P2: `norm_num at h` collapses boss steps

After `have h := add_pow (-1 : ℤ) 2 n`, the learner can do `norm_num at h` to simplify `(-1 + 2)` to `1` and `1 ^ n` to `1` in one step, bypassing the manual `have h2; rw [h2]; rw [one_pow]` sequence. This is a P2 because the learner still needs the key insight (apply `add_pow` with specific values) — the bypass only affects the cleanup steps.

### P2: `one_pow` introduced at the boss

`NewTheorem one_pow` appears on L10 (the boss). This means the learner has never seen `one_pow` before the boss requires it. A small issue since `one_pow` is simple and intuitive, but it violates the principle "bosses integrate, never introduce."

### Technical OK items
- DisabledTactic `trivial decide native_decide simp aesop simp_all` present on all 10 levels — PASS
- TheoremDoc provided for all NewTheorem items — PASS
- TacticDoc provided for `push_cast` — PASS
- DefinitionDoc provided for `Finset.antidiagonal` — PASS
- Build succeeds with no errors — PASS

---

## 8. Ranked Patch List

### P0 (blocking — must fix before R2)

1. **Implement the planned inductive proof (L03-L06)**: Replace the current one-liner levels L03-L06 with the plan's intended content:
   - L03: Base case (n=0) — actual computation showing the sum for n=0 equals 1
   - L04: Inductive step part 1 — expand `(a+b) * (a+b)^n` using the IH
   - L05: Inductive step part 2 — use Pascal's rule to recombine
   - L06: Assembly — combine into the full theorem

   This gives the world its missing proof-move core and retrieves Pascal's rule (M28).

2. **Add `push_cast` supported practice and retrieval**: Add at least one level after L02 where `push_cast` is needed as part of a multi-step proof (e.g., specializing `add_pow` in Z and simplifying the resulting casts manually). Ensure `push_cast` is used in the boss.

3. **Redesign the boss to integrate the world's full repertoire**: The boss should require `push_cast` (L02's tactic), induction/Pascal's rule retrieval (L03-L06's content), and ideally reference Vandermonde or the alternating sum. A boss that only tests `add_pow` specialization is a fake boss for a world that teaches much more.

### P1 (high — fix before R2)

4. **Disable `norm_num` on L02**: Add `norm_num` to the DisabledTactic list on L02 to prevent it from bypassing `push_cast`.

5. **Move `one_pow` introduction before the boss**: Introduce `one_pow` in an earlier level (e.g., in the row sum derivation where 1^m and 1^(n-m) need simplification).

6. **Eliminate or redesign duplicate one-liner levels**: L03 (`exact add_pow x y n` in Z) and L09 (`exact add_pow a b n` in N) are near-clones. L09 is labeled "transfer" but transfers nothing. Either make L09 a genuine transfer exercise (e.g., write a paper-proof outline and fill in Lean steps) or merge with L03.

7. **Make identity-derivation levels multi-step**: L04 (row sum from BT) and L08 (alternating sum) should involve the learner doing the specialization and simplification manually, not just citing a library lemma. For example, L04 should: (a) apply `add_pow` with x=1, y=1, (b) simplify 1^m terms, (c) conclude. L08 should similarly require the learner to specialize `add_pow` at x=1, y=-1 and simplify.

### P2 (medium — fix if time allows)

8. **Add `norm_num` to DisabledTactic on L10**: Prevents `norm_num at h` from collapsing the manual simplification steps in the boss. Not critical since the key insight (specialization) is still required.

9. **Vandermonde levels (L06-L07) are pure library calls**: Consider making at least L07 involve manual computation (expand the antidiagonal sum, compute each term, sum them up) rather than `exact Nat.add_choose_eq 2 3 2`.

---

## 9. What to Playtest Again After Patching

After the P0 and P1 patches:
- **Entire world**: The core levels (L03-L06) will be completely rewritten. Full re-audit required.
- **L02**: Verify `norm_num` is disabled and no other automation closes it.
- **Boss (L10)**: If redesigned, verify seeded subskills, integration quality, and that `norm_num` doesn't bypass.
- **`push_cast` closure**: Verify it appears in at least 3 levels (I, S, G).
- **L04/L08**: If made multi-step, verify hint layering and interactive proof quality.
- **L09 transfer**: If redesigned, verify it's a genuine transfer exercise.

---

## Summary

The world compiles and has correct DisabledTactic baselines, but it is fundamentally broken as a pedagogical unit. 8 of 10 levels are one-liner library calls that teach nothing reusable. The plan's core content (inductive proof of the binomial theorem) was entirely skipped. The new tactic `push_cast` is introduced and orphaned. The boss doesn't integrate the world's repertoire. This world needs a major rewrite, not a patch.
