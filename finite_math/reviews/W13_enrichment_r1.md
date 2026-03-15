# W13 FinsetSum -- Enrichment Review Round 1

## Ranked Suggestions

### 1. L01 introduces `sum_singleton` but L03 re-introduces it -- restructure so L01 teaches notation-only and L03 owns the lemma

**What**: L01 conflates two lessons: (a) introduce big-sum notation, and (b) teach `Finset.sum_singleton`. L03 then asks the learner to "practice" `sum_singleton` with a function argument, but the `NewTheorem` declaration for `sum_singleton` is in L01, so L03 has nothing new to introduce -- it is a repetition level that does not know it is one.

**Why**: The plan says L01's dominant lesson is "Big operator concept + notation" (M23 I, N5 I). Making L01 actually teach a *decomposition lemma* conflates the introduction of notation with the introduction of API. A cleaner structure: L01 does a `norm_num`-style or `rfl`-style computation that shows what the notation *means* without requiring any API lemma, and L03 becomes the true introduction of `sum_singleton` (with `NewTheorem`). This gives each level a single dominant lesson and avoids the "I already did this" feeling in L03.

**Where**: L01 and L03.

**Effort**: Medium (rewrite L01's statement to something that doesn't need `sum_singleton`, move `NewTheorem Finset.sum_singleton` and `TheoremDoc` to L03).

**Recommend**: Yes.

---

### 2. The boss (L09) does not use `sum_cons` or `sum_empty` -- only `sum_insert`, `sum_singleton`, and `sum_union`

**What**: The boss advertises itself as integrating the full world, but it never exercises `sum_cons` (taught in L04) or `sum_empty` (taught in L02). The learner can complete the boss without recalling either.

**Why**: A boss level should require the learner to retrieve the core API taught in the world. `sum_empty` is the base case and `sum_cons` is one of the two decomposition mechanisms. If the boss tests only `sum_insert` and `sum_union`, the learner leaves without ever needing to combine these tools. The plan says the boss covers "Integration of M23, M24" and M24 includes `sum_empty` and `sum_cons`.

**Where**: L09. Redesign the boss statement so it requires at least one `sum_cons` step and one `sum_empty` step alongside the `sum_insert` and `sum_union` steps already present. For example, build a finset that includes a `cons`-constructed part and a segment that reduces to the empty sum.

**Effort**: High (rewrite the boss statement and proof).

**Recommend**: Yes.

---

### 3. L06 (AddCommMonoid) proves commutativity via `omega` -- this trivializes the lesson and bypasses the conceptual point

**What**: L06 asks the learner to prove `f a + sum x in s, f x = sum x in s, f x + f a` and the solution is just `omega`. The level claims to teach "why `Finset.sum` needs `AddCommMonoid`," but the proof does not involve `AddCommMonoid` at all -- it uses `omega` on `Nat`, which already knows commutativity.

**Why**: This is the misconception level for C8. The level's introduction does an excellent job explaining *why* commutativity matters, but the proof exercise does not make the learner *use* that understanding. `omega` is a black box that closes arithmetic goals without the learner engaging with commutativity as a concept. A stronger exercise would either: (a) work over a general `AddCommMonoid` (so the learner must use `add_comm` explicitly), or (b) present a non-commutative operation and show that reordering fails (a "what-if" level). Option (a) is more practical: make the statement `(M : Type) [AddCommMonoid M] (a : M) (s : Finset M) (f : M -> M) : f a + sum x in s, f x = sum x in s, f x + f a` and have the learner use `add_comm`.

**Where**: L06.

**Effort**: Medium (change the statement to use a general `AddCommMonoid` instead of `Nat`, update hints to guide toward `add_comm`).

**Recommend**: Yes.

---

### 4. No level teaches `sum_filter` -- a plan coverage item (M24) that is listed but never appears

**What**: M24 includes `sum_filter` in its definition: "Big operator basic API: `sum_empty`, `sum_cons`, `sum_singleton`, `sum_union`, `sum_filter`." The world teaches the first four but not `sum_filter`.

**Why**: `sum_filter` is one of the most useful API lemmas in practice: `sum x in s.filter p, f x = sum x in s, if p x then f x else 0`. It connects filtering to conditional sums and is prerequisite for inclusion-exclusion (W17 per the plan). Omitting it leaves M24 incomplete at the (S) coverage level.

**Where**: New level between L08 and L09 (or replace the current L08 position and push the boss). Alternatively, integrate it as a second exercise in L08.

**Effort**: High (new level).

**Recommend**: Yes.

---

### 5. `Finset.prod` is never mentioned -- the plan's M23 item covers both `sum` and `prod`

**What**: M23 is defined as "`Finset.sum` and `Finset.prod`" in the content map. The world title and all 9 levels deal exclusively with `sum`. The multiplicative analogues (`prod_empty`, `prod_singleton`, `prod_cons`, `prod_insert`, `prod_union`) are never mentioned, even in passing.

**Why**: The learner should at least *know* that `Finset.prod` exists and has an identical API. This does not require a new level -- a paragraph in the world conclusion (L09) pointing out the parallel would suffice. Something like: "Everything you learned about `sum` has a multiplicative counterpart: `Finset.prod`, with `prod_empty`, `prod_singleton`, `prod_insert`, and `prod_union`. The requirement changes from `AddCommMonoid` to `CommMonoid`."

**Where**: L09 conclusion.

**Effort**: Low (add a paragraph to the conclusion).

**Recommend**: Yes.

---

### 6. The "decompose-then-evaluate" proof strategy is used in L07 and L09 but never named

**What**: Both L07 and L09 follow the same proof pattern: (1) repeatedly apply `sum_insert` or `sum_cons` to peel off elements, (2) apply `sum_singleton` to the last element, (3) close with arithmetic. This pattern is the core operational skill of the world, but it is never given a name.

**Why**: Naming a proof strategy makes it retrievable. When the learner encounters a concrete-sum computation in a later world (W14, W14_ex, or a pset), they should be able to think "this is the decompose-then-evaluate strategy" rather than re-deriving the approach. The L07 conclusion mentions "the decomposition pattern" informally but does not name it as a strategy the learner should remember.

**Where**: L07 conclusion (name the strategy explicitly) and L09 introduction (reference it by name).

**Effort**: Low (add/edit text in conclusions).

**Recommend**: Consider.

---

### 7. No level explores what happens when `sum_insert` is applied with a *member* element -- the disjointness/non-membership requirement is never stressed

**What**: Both `sum_cons` and `sum_insert` require `a not in s`. The world treats this as a minor technical detail (provide `by norm_num` proofs). But the learner never sees what goes wrong when the hypothesis is violated.

**Why**: Understanding *why* non-membership is needed is more valuable than being able to prove it. If `a in s`, then `insert a s = s`, so `sum x in insert a s, f x = sum x in s, f x`, not `f a + sum x in s, f x`. This is a double-counting issue. A brief remark in L05's conclusion showing the failure case would reinforce the lesson without requiring a new level.

**Where**: L05 conclusion.

**Effort**: Low (add a paragraph explaining the failure case).

**Recommend**: Consider.

---

### 8. L08 (`sum_union`) uses `norm_num [Finset.disjoint_left]` to prove disjointness but this tactic combination is never taught

**What**: The learner is asked to prove `Disjoint {1,2} {3,4}` using `norm_num [Finset.disjoint_left]`, but `Finset.disjoint_left` is not in the inventory and `norm_num` with a custom lemma argument is a Lean idiom that has not been explained.

**Why**: If the learner has never seen `norm_num [lemma_name]` before, this will feel like a trick. Either the level should teach this idiom explicitly (a sentence in the introduction explaining "you can feed lemmas to `norm_num`"), or the disjointness proof should be provided as a `have` in the template so the learner focuses on `sum_union` rather than disjointness mechanics.

**Where**: L08 introduction or hints.

**Effort**: Low (add explanatory text).

**Recommend**: Consider.

---

### 9. The connection between `Finset.sum` and `Finset.card` is mentioned in the L08 conclusion but never made into a level

**What**: L08's conclusion notes that "cardinality is the special case of summing the constant function `1`." This is a beautiful mathematical fact: `s.card = sum x in s, 1`. But the learner never proves it.

**Why**: Deriving `card` as a special case of `sum` is a "derivable result presented as axiom" opportunity. The learner already knows `Finset.card` from earlier worlds. Showing that `card` is `sum (fun _ => 1)` connects two concepts and demonstrates that `sum` generalizes `card`. This could be a level between L07 and L08, or it could be integrated into L06 as a more meaningful exercise than the current commutativity proof.

**Where**: New level, or modify an existing level to include this derivation.

**Effort**: Medium (new level or significant level rewrite).

**Recommend**: Consider.

---

### 10. L01's `TheoremDoc` for `sum_singleton` shows a fully general type signature that may confuse learners at this stage

**What**: The introduction displays the full polymorphic signature: `Finset.sum_singleton : forall {beta : Type u_1} {alpha : Type u_2} [inst : AddCommMonoid beta] (f : alpha -> beta) (a : alpha), sum x in {a}, f x = f a`. This is the raw Lean signature with universe polymorphism and instance arguments.

**Why**: Learners at this stage are not expected to parse universe variables (`u_1`, `u_2`) or implicit instance arguments. The signature will look intimidating. A simplified version like `Finset.sum_singleton (f : alpha -> beta) (a : alpha) : sum x in {a}, f x = f a` would convey the same information without the noise.

**Where**: L01 introduction.

**Effort**: Low (edit the displayed signature).

**Recommend**: Consider.

---

## Overall Impression

The world does a solid job introducing the basic `Finset.sum` API in a logical progression: notation, base case (empty), singleton, cons, insert, the AddCommMonoid motivation, concrete computation, union, and boss. The introductions are well-written with clear mathematical explanations, and the cons-vs-insert comparison (L04/L05) is particularly well handled. The conclusions consistently include "in plain language" transfer moments.

The single most important improvement is **suggestion 3 (L06 AddCommMonoid)**. This is the world's only misconception level and its only "why" level, yet the proof exercise (`omega`) completely bypasses the conceptual lesson. Changing the statement to work over a general `AddCommMonoid` -- so the learner must explicitly invoke `add_comm` -- would transform a check-the-box level into a genuine insight moment. The current version teaches commutativity in the introduction but then tests "can you type `omega`."
