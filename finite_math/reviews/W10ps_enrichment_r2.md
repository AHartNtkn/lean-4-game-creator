# W10_ps FinsetPset — Enrichment Review (Round 2)

## R1 fix verification

**Fix: `omega` added to DisabledTactic on L05 (`InductionOnNewProperty`).**
Verified. L05 line 62 now reads `DisabledTactic trivial decide native_decide aesop simp_all omega`. This prevents the learner from closing the entire induction proof with `omega` alone (which would bypass both the `induction` step and `Finset.card_insert_of_notMem`). Fix is correct and complete.

---

## Ranked suggestions

### 1. `simp` is not disabled in any of the 8 levels

**What**: All 8 levels disable `trivial decide native_decide aesop simp_all` but not `simp`. The project's standard disabled set (from project memory) is `trivial decide native_decide simp aesop simp_all`.

**Why**: This is a systemic issue. In a problem set world that is supposed to test retrieval under reduced scaffolding, leaving `simp` enabled defeats the purpose for several levels:

- **L01**: `simp [Finset.mem_insert, Finset.mem_singleton]` is the *intended* proof. This is fine — `simp` with explicit lemma arguments is the skill being tested. But bare `simp` or `simp only []` with auto-discovered lemmas also closes the goal, letting the learner avoid specifying which lemmas to use. The retrieval value is in knowing *which* lemmas to pass to `simp`.
- **L02**: `simp` can close the subset goal after `intro a ha` and the membership rewriting step.
- **L03**: `simp [Finset.inter_comm, Finset.inter_assoc]` or just `ext; simp` can close the absorption law without the learner manually constructing the `mem_inter`/`mem_union` argument.
- **L04**: The `have` subgoal uses `simp only [...]` in the model proof, but bare `simp` with auto-lemma discovery might also close it.
- **L08 (Boss)**: `simp [Finset.mem_insert, Finset.mem_singleton]` handles Part 1, and `simp [Finset.mem_sdiff, Finset.mem_inter]` can partially solve the goal without the learner manually applying `Finset.mem_sdiff`.

The problem set is supposed to measure what the learner retained. `simp` without specific lemma arguments is a memory bypass. Disabling `simp` forces the learner to recall the specific membership lemmas and proof patterns.

**Where**: Add `simp` to the `DisabledTactic` line in all 8 levels. Then update the model proofs that currently use `simp` — replace them with `simp only [...]` equivalents or manual `rw`/`exact` chains. The model proofs in L01, L02, L04, and L08 all use `simp` and would need to be adjusted to use `simp only` or manual alternatives.

**Effort**: Medium (add one word to 8 DisabledTactic lines, but also must audit and potentially rewrite model proofs that rely on bare `simp`).

**Recommend**: Yes.

---

### 2. L05 teaches finset induction retrieval but the target statement (`card s <= card s + card s`) is trivially true and does not exercise the inductive hypothesis meaningfully

**What**: L05 proves `s.card ≤ s.card + s.card`. The base case is `0 ≤ 0 + 0` (trivial). The insert step rewrites `card (insert a s')` to `card s' + 1` using `card_insert_of_notMem ha`, then closes with `omega`. The inductive hypothesis `ih : s'.card ≤ s'.card + s'.card` is available but `omega` closes the arithmetic without the learner needing to explicitly invoke `ih`.

**Why**: The plan says L05 should be "retrieval of V4" — the learner should practice the full finset induction pattern. But in the current implementation, `omega` handles all the arithmetic automatically (even with `omega` disabled, `linarith` or manual arithmetic would also work without referencing `ih`). The statement `n + 1 ≤ (n + 1) + (n + 1)` is true independently of `ih`, so the insert step never forces the learner to use the inductive hypothesis. This makes L05 essentially a syntax drill ("can you type `induction s using Finset.induction_on`?") rather than a retrieval of the full induction pattern.

A better target would be a statement where `ih` is genuinely needed, such as:
- `2 * s.card = s.card + s.card` (Nat induction on card, but exercises the insert step with `ih`)
- `(s.filter p).card ≤ s.card` (requires `ih` in the insert step)
- `s.card + 1 ≤ (insert a s).card + 1` given `a ∉ s` (directly exercises `card_insert_of_notMem` with `ih`)

**Where**: L05 — change the statement to one where the insert step requires explicit use of `ih`.

**Effort**: Medium (rewrite the statement and proof).

**Recommend**: Yes.

---

### 3. L03 proves the absorption law but the conclusion does not name it as a lattice identity or connect it to the broader pattern

**What**: L03 proves `s ∩ (s ∪ t) = s`, which the introduction correctly calls the "absorption law." The conclusion mentions it is "a standard identity in lattice theory" but does not explain what this means or connect it to the dual absorption law `s ∪ (s ∩ t) = s`.

**Why**: The absorption laws are the defining identities of lattices, and finsets form a lattice under ∪ and ∩. The learner has just proved one of the two absorption laws. Mentioning the dual — even just "the other absorption law, `s ∪ (s ∩ t) = s`, can be proved by the same technique" — costs one sentence and creates a forward link to the `orders_lattices` course (Course 3 in the priority order). More importantly, it reinforces the ext+membership pattern by suggesting the learner could try the dual as an exercise.

**Where**: L03 conclusion — add one sentence about the dual absorption law and the lattice connection.

**Effort**: Low (one sentence).

**Recommend**: Consider.

---

### 4. L06 and L07 are one-lemma application levels with minimal retrieval demand — the transfer value could be strengthened

**What**: L06 proves inclusion-exclusion by `exact Finset.card_union_add_card_inter _ _`. L07 proves subset-cardinality by `exact Finset.card_le_card h`. Both are single-tactic proofs. The pedagogical value is supposed to come from the "paper version" in the conclusion (transfer levels). However, the paper versions are given to the learner, not constructed by them.

**Why**: Transfer is strongest when the learner actively produces the translation, not when they passively read it. In both levels, the Lean proof is one step and the conclusion provides the paper version. The learner does no work on the translation. For a problem set world whose purpose is retrieval, these levels are unusually passive.

Consider adding a "Transfer question" to the introduction of one of these levels: "Before you prove this in Lean, write down (on paper or in your head) what the claim says and why it is true. Then apply the Lean lemma." This makes the transfer active rather than passive. Alternatively, the introduction could present a slightly different formulation (e.g., the subtractive form of inclusion-exclusion) and ask the learner to connect it to the additive form.

**Where**: L06 or L07 introduction — add a sentence encouraging the learner to state the paper version before writing the Lean proof.

**Effort**: Low (a sentence in the introduction).

**Recommend**: Consider.

---

### 5. L08 (Boss) Part 2 (`s ∩ t ⊆ s`) is a standalone fact that was already proved as a library lemma — the boss should test integration, not re-derivation of a known lemma

**What**: Part 2 of the boss asks the learner to prove `s ∩ t ⊆ s` for arbitrary finsets. This is `Finset.inter_subset_left` in mathlib. The learner proves it by `intro a ha; rw [Finset.mem_inter] at ha; exact ha.1`. This is the same pattern as L02 (subset from a condition) and L03 (absorption law), both of which already exercise `mem_inter` and the subset intro pattern.

**Why**: In a boss level that is supposed to integrate skills from across Module C, repeating the same subset-intro + mem_inter pattern a third time does not test anything new. The boss already tests membership (Part 1 with `mem_sdiff`) and cardinality (Part 3 with inclusion-exclusion + `omega`). Part 2 could be replaced with something that tests a skill not yet exercised in this world — for example:
- A filter-based subset: `Finset.filter p s ⊆ s` (retrieves M8 from L04)
- An image membership: `a ∈ s → f a ∈ Finset.image f s` (retrieves M8)
- A cardinality-from-subset result: prove `(s ∩ t).card ≤ s.card` (combines subset + cardinality, retrieves both V14 and V15)

Any of these would give the boss a wider integration footprint without increasing difficulty.

**Where**: L08 Part 2 — replace `s ∩ t ⊆ s` with a different intermediate part that tests a skill not already covered in L01-L03.

**Effort**: Medium (rewrite one part of the boss).

**Recommend**: Consider.

---

### 6. The world conclusion's retrieval table references world numbers (W6, W7, W8, W9, W10) but the learner has no way to know what those world numbers mean

**What**: The L08 conclusion contains a retrieval table mapping each level to a skill code and a "From world" column with entries like "W6", "W7", "W8, W9", "W10". The learner playing the game does not see world numbers — they see world names.

**Why**: This is a minor presentation issue. The table would be more useful if it used world names (e.g., "Membership and simp", "Union, intersection, and ext", "Cardinality") instead of numbers. The skill codes (V5, V14, V6, V7, M8, M9, V4, T4, T3) are internal plan identifiers that similarly mean nothing to the learner. Replacing them with descriptive names would make the retrieval table a genuine self-assessment tool rather than an opaque reference.

**Where**: L08 conclusion — replace world numbers and skill codes with descriptive names.

**Effort**: Low (text editing).

**Recommend**: Consider.

---

### 7. No level in the world exercises `Finset.sdiff` (`\`) reasoning before the boss demands it in Part 1

**What**: L08 Part 1 asks the learner to prove `7 ∈ {5, 7, 9, 11} \ {9, 11, 13}`, which requires `Finset.mem_sdiff`. But no earlier level in this world (L01-L07) exercises set difference. The learner's most recent exposure to `sdiff` was in W7 (Union, intersection, difference, and `ext`), potentially many sessions ago.

**Why**: The boss is supposed to integrate skills from throughout Module C. Set difference is one of those skills. But the problem set world itself never warms up this skill — it goes straight to the boss. Every other boss component (membership in L01, subset in L02, ext+set ops in L03, filter in L04, induction in L05, inclusion-exclusion in L06, subset-cardinality in L07) has a warm-up level. Set difference is the only skill that appears in the boss without a preceding warm-up.

This could be addressed by either (a) adding a brief `sdiff` level (e.g., "Prove `3 ∈ {1, 2, 3, 4} \ {2, 4}`") before the boss, or (b) replacing one of the less distinctive levels (e.g., L01, which is very similar to L02 in technique) with an `sdiff` membership problem.

**Where**: A new level before L08, or replace L01 with an `sdiff` membership problem.

**Effort**: Medium (adding or replacing a level).

**Recommend**: Consider.

---

### 8. The world does not foreshadow `Fintype` (W11) — the conclusion mentions it but does not explain why it matters

**What**: L08's conclusion ends with "The next world introduces **`Fintype`**: the type class that equips a type with a universal finset `Finset.univ`, enabling type-level counting via `Fintype.card`." This is a factual preview but not a motivational one.

**Why**: After 8 levels of working with specific finsets like `{5, 7, 9, 11}`, the learner might wonder: "Why do I keep writing out finset literals? Isn't there a way to talk about *all* elements of a type at once?" This is exactly what `Fintype` provides. A sentence that connects the current frustration to the upcoming tool — e.g., "You may have noticed that we keep constructing finsets by hand. The next world introduces `Fintype`, which gives you a finset containing *every* element of a type, so you can reason about all elements without listing them" — would make the transition feel motivated rather than arbitrary.

**Where**: L08 conclusion — expand the `Fintype` preview to connect it to the learner's experience in this world.

**Effort**: Low (one-two sentences).

**Recommend**: Consider.

---

## Overall impression

The world fulfills its plan-specified purpose: it retrieves finset skills (membership, subset, ext, filter, induction, inclusion-exclusion, subset-cardinality) under reduced scaffolding with fresh surface forms. The level ladder maps cleanly to the plan's 8-level outline, and each level targets a distinct skill from Module C. The transfer levels (L06-L07) include well-written paper-proof translations with worked examples. The boss (L08) is a genuine integration exercise combining three distinct proof patterns — membership in a set difference, subset via intersection, and union cardinality via inclusion-exclusion. The `omega` fix on L05 is correctly implemented.

**The single most important improvement** is disabling `simp` across all 8 levels (suggestion #1). A problem set world is specifically designed to test retrieval, and `simp` is the primary memory bypass available to the learner. Without disabling it, the learner can solve most levels without recalling any specific membership or set-operation lemma names. This is a standard disabled-tactic fix (the same issue has been caught and fixed in prior worlds). The secondary priority is strengthening L05 (suggestion #2) so that finset induction retrieval genuinely exercises the inductive hypothesis rather than serving as a syntax-only drill.
