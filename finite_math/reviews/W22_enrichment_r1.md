# W22 PermutationWorld -- Enrichment Review (Round 1)

**Reviewer**: enrichment-reviewer
**Date**: 2025-03-15
**Files reviewed**: L01_PermDef.lean through L07_Boss.lean (7 levels)
**Plan reference**: PLAN.md lines 748-760 (W22)

---

## Ranked suggestions

### 1. The boss level diverges from the plan: it uses `pow_card_eq_one` instead of exhaustion over permutations (V2)

**What**: The plan specifies the boss should "Prove a property of all permutations of `Fin 3` using exhaustion" and tags V2 (case splitting/exhaustion on `Fin n`) as a coverage item. The actual boss uses `pow_card_eq_one` (Lagrange's theorem), which is a beautiful result but does not exercise exhaustion at all.

**Why**: V2 is a core proof move for this course (introduced in W2, revisited in W3_ex, culminating here and in W24). The plan's coverage table explicitly marks W22.L07 as covering "Integration of M36, V2" with M36 (G). If the boss never requires the learner to enumerate or case-split over `Equiv.Perm (Fin 3)`, the V2 coverage gap is real. Moreover, applying `pow_card_eq_one` is a one-step "magic lemma" move -- the learner does not build mathematical intuition about *which* permutations exist. An exhaustion-based boss (e.g., "prove that every permutation of `Fin 3` satisfies `sigma^3 = 1` or `sigma^2 = 1`" by enumerating all six permutations) would be far more instructive and would exercise V2 as planned. The current `pow_card_eq_one` result (sigma^6 = 1) is strictly weaker than the order-divides result and does not require the learner to think about what S_3 actually looks like.

**Where**: L07_Boss.lean -- replace or restructure the boss.

**Effort**: High (rewrite the boss level).

**Recommend**: Yes. This is a plan compliance issue that also happens to be a genuine pedagogical gap: the learner completes the permutation world without ever seeing what S_3 looks like concretely.

---

### 2. Missing: an inverse level -- the group structure is incomplete without `sigma^{-1}`

**What**: The world teaches identity (L04), composition (L03), and mentions associativity in passing, but never has the learner compute an inverse. L04 mentions `Equiv.swap_mul_self` in the conclusion (swaps are self-inverse), but the learner never *uses* it in a proof. A level where the learner proves `Equiv.swap a b * Equiv.swap a b = 1` (or equivalently, computes `sigma^{-1}` for a specific permutation) would complete the group-structure preview.

**Why**: The world promise says the learner should understand `Equiv.Perm (Fin n)` as "the group of permutations." A group has four ingredients: closure under composition, associativity, identity, and inverses. The world covers composition (L03), identity (L04), and mentions associativity, but inverses are only mentioned in a conclusion paragraph. This is a genuine missing piece of mathematical depth -- the derivation "a swap is its own inverse" is simple, concrete, and reinforces both `mul_def` and `one_def`.

**Where**: New level between L04 (Identity) and L05 (Counting), or modify L04 to make the self-inverse property the actual proof goal instead of a conclusion sidebar.

**Effort**: Medium (add a new level or restructure L04 to include a proof of `swap_mul_self` or a derived consequence).

**Recommend**: Yes.

---

### 3. No non-commutativity level -- the plan's own table has no such level, but the world badly needs one

**What**: The world never shows the learner that permutation composition is non-commutative. The plan table for W22 does not include such a level, but this is an oversight in the plan itself. The learner should see a concrete example: `swap 0 1 * swap 1 2 != swap 1 2 * swap 0 1` on `Fin 3`.

**Why**: Non-commutativity is one of the most important conceptual takeaways from symmetric groups. The introduction to L03 warns about order ("first apply tau, then sigma"), but the learner never sees it *matter*. A level that computes both `(swap 0 1 * swap 1 2)(0)` and `(swap 1 2 * swap 0 1)(0)` and shows they differ would make the warning visceral. Without this, the learner could leave thinking "order doesn't really matter" since every example they work happens to be evaluated at a single point. This is a classic "misconception level" opportunity.

**Where**: New level after L03 (Composition).

**Effort**: Medium (new level proving `swap 0 1 * swap 1 2 != swap 1 2 * swap 0 1` via evaluation at a specific point, or proving the two compositions give different results at `0`).

**Recommend**: Yes.

---

### 4. L05 (Counting) uses `Fin 4` but the rest of the world uses `Fin 3` -- lost opportunity for coherence

**What**: L05 proves `card (Equiv.Perm (Fin 4)) = 24`, while every other level works with `Fin 3`. The boss then reproves `card (Equiv.Perm (Fin 3)) = 6` as Part 1. If L05 proved the `Fin 3` case (= 6), the boss could simply *use* that result without re-deriving it, and the world would feel more unified.

**Why**: Using `Fin 4` in L05 introduces a type the learner never otherwise works with in this world, and the switch feels unmotivated. Using `Fin 3` would make the counting feel like a continuation of the concrete examples from L01-L04. The boss could then build on L05's result directly. Alternatively, if the pedagogical reason for `Fin 4` is "show that n! grows fast," that motivation should be stated explicitly.

**Where**: L05_CountingPerms.lean and L07_Boss.lean.

**Effort**: Low (change `Fin 4` to `Fin 3` in L05, and 24 to 6; adjust factorial unfolding accordingly; simplify boss Part 1 to reference the earlier result).

**Recommend**: Consider. The current approach works, but the coherence gain from sticking with `Fin 3` throughout is meaningful.

---

### 5. L06 (List.Perm vs Equiv.Perm) is a one-step `exact` level -- no real engagement with the distinction

**What**: The level asks the learner to prove `[1, 0, 2].Perm [0, 1, 2]` and the solution is `exact List.Perm.swap 0 1 [2]`. The introduction does an excellent job explaining the conceptual distinction, but the proof exercise does not require the learner to *grapple* with the distinction at all. They just call one constructor.

**Why**: The level's dominant lesson is misconception C12 -- understanding that `List.Perm` and `Equiv.Perm` are fundamentally different things. But the proof only uses `List.Perm`; the learner never has to confront the difference in a proof. A stronger design would ask the learner to prove something involving both concepts -- for example, prove `[1, 0, 2].Perm [0, 1, 2]` AND show that applying `swap 0 1` to the list `[0, 1, 2]` via `List.map` produces `[1, 0, 2]`, making the connection between the two notions explicit. Alternatively, a two-part statement: (a) `[1, 0, 2] ~ [0, 1, 2]` using `List.Perm`, and (b) `(Equiv.swap 0 1) 0 = 1 /\ ...` using `Equiv.Perm`, so the learner sees both in one level.

**Where**: L06_ListPermVsEquivPerm.lean.

**Effort**: Medium (restructure the level to include both concepts in the proof goal).

**Recommend**: Yes. A misconception level that only exercises one side of the misconception is underperforming its role.

---

### 6. The "evaluation pattern" for compositions is unnamed -- it's used in L03 and again in L07 implicitly

**What**: L03's conclusion articulates a 4-step pattern for evaluating `(sigma * tau) x`: (1) `mul_def`, (2) `trans_apply`, (3) evaluate inner, (4) evaluate outer. This pattern is used in L03 and would be used again if the boss involved concrete computation. But it is never given a name like "the composition evaluation pattern" or "the peel-and-evaluate strategy."

**Why**: Naming proof strategies is a key part of building proof-move fluency. The pattern is mechanical and repeatable -- exactly the kind of thing that benefits from being named so the learner can recall it later. The L03 conclusion's numbered list is close to this, but framing it as a named strategy (even just in a sentence like "We call this the *peel-and-evaluate* pattern for permutation composition") would make it more memorable and transferable.

**Where**: L03_Composition.lean, conclusion text.

**Effort**: Low (add one sentence naming the pattern).

**Recommend**: Consider.

---

### 7. No foreshadowing of sign/parity -- missed low-cost transfer opportunity

**What**: The world never mentions that permutations have a *sign* (even or odd), which is one of the most important properties of permutations for later algebra. Since the world already computes compositions of transpositions, a sentence in the L03 conclusion like "It turns out that the number of transpositions needed to express a permutation has a well-defined parity -- this is the *sign* of a permutation, a concept you will meet if you study group theory further" would plant a seed at zero cost.

**Why**: The sign of a permutation is the single most important structural fact about S_n beyond its group structure. Since the world already works with transpositions and their compositions, the connection is natural. A brief mention would aid transfer for learners who go on to study algebra.

**Where**: L03_Composition.lean conclusion, or L07_Boss.lean conclusion.

**Effort**: Low (one or two sentences in a conclusion).

**Recommend**: Consider.

---

### 8. L04 introduces `Equiv.swap_mul_self` as a `NewTheorem` but the learner never uses it

**What**: L04 adds `Equiv.swap_mul_self` to the inventory (`NewTheorem Equiv.Perm.one_def Equiv.swap_mul_self`), but no subsequent level requires or even encourages the learner to use it. It is only mentioned in the conclusion text.

**Why**: Introducing a theorem to inventory without ever requiring its use is pedagogically confusing -- the learner sees it in their theorem panel and wonders when to use it. Either there should be a level that uses it (see suggestion #2 about an inverse level), or it should not be added to inventory until it is needed.

**Where**: L04_Identity.lean (remove from `NewTheorem` if no inverse level is added, or add an inverse level that uses it).

**Effort**: Low (remove from `NewTheorem`) or medium (if paired with a new inverse level per suggestion #2).

**Recommend**: Yes (either add a level that uses it, or remove it from inventory).

---

### 9. The world introduction in L01 mentions S_n has n! elements, but this is not proved until L05 -- potential confusion

**What**: L01's introduction states "The set of all permutations of an n-element set forms a group called the symmetric group S_n, with n! elements." This is a forward reference to L05's content. By the time the learner reaches L05, this fact may feel like a rederivation of something already stated as true.

**Why**: The introduction could instead say something like "...forming a group called the symmetric group S_n -- you will prove that it has n! elements later in this world" to signal that this is a fact to be earned, not a given. This small change preserves the motivating information while making clear that L05 will do the work.

**Where**: L01_PermDef.lean introduction text.

**Effort**: Low (edit one sentence).

**Recommend**: Consider.

---

### 10. `omega` is used in hints (L02, L03) but never declared with `NewTactic`

**What**: L02 and L03 both have hints telling the learner to use `by omega` to close inequality goals, but `omega` is never declared via `NewTactic` in this world. If `omega` was introduced in an earlier world (W1 or W2 per the plan), this may be fine, but it should be verified that the learner's tactic panel shows `omega` as available.

**Why**: If `omega` is not in the learner's inventory panel, the hint to "use `by omega`" will feel like an unexplained trick. This is a minor Lean-expression layer gap.

**Where**: L02_ConcreteSwap.lean or L01_PermDef.lean (add `NewTactic omega` if not inherited from earlier worlds).

**Effort**: Low (verify and potentially add one line).

**Recommend**: Consider (verify first whether it is inherited).

---

## Overall impression

The world has strong foundations: the introductions are well-written with good mathematical context, the progression from swap evaluation (L01-L02) through composition (L03) and identity (L04) to counting (L05) is logical, and the C12 misconception level (L06) addresses a genuine point of confusion. The inventory management is mostly clean, and the disabled tactic list is appropriate.

The single most important improvement is **suggestion #1: the boss level must exercise exhaustion (V2) as the plan specifies**, not `pow_card_eq_one`. The current boss is a clever application of Lagrange's theorem, but it sidesteps the core proof move this world is supposed to culminate in. A boss that requires the learner to enumerate permutations of `Fin 3` (even just a few of them) would be far more valuable for building concrete understanding of symmetric groups. This change would naturally address the secondary concern that the learner never sees what S_3 actually looks like -- currently, S_3 remains a black box whose cardinality is computed but whose elements are never enumerated.
