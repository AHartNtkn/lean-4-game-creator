# W13 FinsetSum — Enrichment Review Round 2

**Reviewer**: lean4game-enrichment-reviewer
**World**: W13 FinsetSum (9 levels, L01–L09)
**Round**: R2 (follow-up to R1)
**Date**: 2025-03-15

## R1 Fix Verification

1. **L07 `norm_num` exploit** (R1 Yes): FIXED. `norm_num` is now in L07's DisabledTactic line. The level requires the learner to do the step-by-step decomposition (`sum_insert` + `sum_singleton`) manually. However — see item 1 below: `norm_num` is still available as the final arithmetic closer, but `norm_num` is used only *within* `have` proofs for membership and for the final arithmetic step. The level's pedagogical flow (three explicit rewrites) is preserved. Verified.

2. **L06 AddCommMonoid prose-only** (R1 Yes, deferred): L06 demonstrates commutativity concretely via a proof (`omega` closes `f a + S = S + f a`), and the conclusion explains AddCommMonoid's three components. This follows the established pattern (cf. W5 L06 for DecidableEq). Adequate.

## New Suggestions

### 1. L07 still closable by `omega` alone

**What**: With `norm_num` disabled, the goal `∑ x ∈ ({1, 2, 3} : Finset Nat), (x ^ 2) = 14` may still be closable by `omega` if the sum normalizes under `omega`'s preprocessing. Even if it doesn't close the full goal today, `omega` might close the final arithmetic subgoal after partial rewrites, which is fine — but the real concern is whether a learner can skip the entire decomposition by using a single `omega` or `native_decide`.

**Why**: `native_decide` is already disabled. `omega` is not disabled. If `omega` alone closes the full goal (it likely does not, since `omega` doesn't know `Finset.sum`), this is a non-issue. But if `omega` closes intermediate goals that should require `sum_insert` + `sum_singleton`, the level's pedagogy is undermined. The actual risk is low: `omega` won't simplify `Finset.sum` terms. The final `norm_num` step (line 59 in the solution) is now blocked by the DisabledTactic. The learner must use the rewrites.

**Where**: L07
**Effort**: Low (verify and document, no change needed if `omega` doesn't close the full goal)
**Recommend**: Consider — verify that `omega` alone does not close the goal. If it does, add `omega` to L07's DisabledTactic.

### 2. No `sum_add_distrib` or linearity lemma

**What**: The world teaches decomposition (peeling elements off) but never mentions that `Finset.sum` distributes over addition: `∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + ∑ x ∈ s, g x`. This is `Finset.sum_add_distrib`.

**Why**: `sum_add_distrib` is one of the most-used `Finset.sum` lemmas in practice. It is the formal expression of linearity of summation — a concept every calculus student knows intuitively ("the sum of sums is the sum of the sums"). The plan assigns it to later worlds (W15/W16 under algebraic manipulation), so it does not belong here. But a one-sentence mention in L09's conclusion ("Next you'll learn that sums distribute over addition...") would seed the vocabulary.

**Where**: L09 conclusion (one sentence)
**Effort**: Low
**Recommend**: Consider — the plan already places this in W15/W16; a forward reference in L09's conclusion is helpful but not critical.

### 3. L09 boss does not require `sum_empty` — a dead lemma

**What**: L02 teaches `sum_empty`, but it is never used again in this world. L09 (boss) combines `sum_union`, `sum_insert`, `sum_singleton`, and arithmetic — but never requires `sum_empty`. The learner learns `sum_empty` and then forgets it.

**Why**: A lemma taught but never retrieved in the same world risks feeling pointless. The plan shows `sum_empty` as M24 (I) = introduced, meaning it will be retrieved later (W14 for induction base cases). This is acceptable — not every lemma needs same-world retrieval. But the boss could be slightly richer if it included an empty-set component.

**Where**: L09
**Effort**: Medium (would require restructuring the boss statement to include an empty-set term)
**Recommend**: Consider — `sum_empty` retrieval in W14 (induction base case) is the natural place. Forcing it into L09 would feel contrived.

### 4. L04 and L05 are structurally identical — missed contrast opportunity

**What**: L04 (sum_cons) and L05 (sum_insert) present nearly identical proofs (`exact Finset.sum_cons ha` vs `exact Finset.sum_insert ha`) with identical proof structures. The conclusion of L05 mentions the difference (cons requires upfront proof, insert uses DecidableEq), but the levels themselves don't make the learner *feel* the difference.

**Why**: The pedagogical opportunity is to show that `cons` and `insert` behave differently when `a ∈ s`. `insert a s = s` when `a ∈ s` (idempotent), but `cons a s h` is only defined when `a ∉ s`. A level that demonstrates this contrast — e.g., asking the learner to compute `∑ x ∈ insert 2 {2, 3}, f x` where `insert` is a no-op — would make the distinction visceral. However, the plan's level descriptions match exactly what's implemented, and the cons-vs-insert distinction was already covered in earlier worlds (W6 for insert idempotence, C7 misconception). Repeating it here would be redundant.

**Where**: L04–L05
**Effort**: Medium (adding a level or modifying L05)
**Recommend**: Consider — the distinction is taught in W6 and W10. The prose in L05's conclusion is sufficient for this world's scope.

### 5. The world never uses `Finset.sum` with a non-trivial function on integers or rationals

**What**: Every level uses `Nat` as the codomain. The introduction (L01) and conclusion (L03, L06) mention that `Finset.sum` works for `Int`, `Rat`, `Real`, but the learner never works with anything other than `Nat`.

**Why**: This is a missed concreteness opportunity. Seeing `Finset.sum` work with `Int` (where subtraction exists) or `Rat` (where division exists) would reinforce that the API is generic. However, introducing `Int` or `Rat` in this world would add type annotation complexity that could distract from the core lesson (the sum API). The plan places multi-type examples in later worlds.

**Where**: Potentially a new level between L07 and L08, or a modification of L07
**Effort**: Medium
**Recommend**: Consider — the plan's scope for W13 is "definition and basic lemmas." Multi-type examples fit better in W14_ex (examples world). The prose mentions suffice for now.

## Overall Impression

The world is solid and well-structured. The level ladder follows a clean progression: notation introduction (L01), base case (L02), singleton (L03), cons decomposition (L04), insert decomposition (L05), the "why" of AddCommMonoid (L06), concrete computation (L07), union splitting (L08), boss integration (L09). The R1 fix for `norm_num` in L07 is correctly applied.

The single most important observation is that all suggestions are "consider" rather than "yes" — the world is clean. The R1 fixes addressed the two substantive issues. No new "yes" items found. The world is ready to pass.

## Verdict

**CLEAN** — no Yes items. Five Consider items noted for optional future improvement. R1 fixes verified.
