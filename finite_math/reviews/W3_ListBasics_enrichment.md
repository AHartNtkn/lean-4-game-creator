# Enrichment Review: W3 ListBasics

## Ranked suggestions

### 1. The plan's `List.Nodup` level (L07 in the plan) is entirely missing

**What**: The plan specifies level 7 as "Prove a specific list has no duplicates, and show one that does" introducing `List.Nodup` (M17). The implemented world has no `Nodup` level at all; the slot is occupied by `List.reverse`, which is not in the plan.

**Why**: `List.Nodup` is a load-bearing concept for the course. W4 (Multisets) relies on it: level W4.2 uses `List.Perm` and M17, and the entire List -> Multiset -> Finset hierarchy story depends on the learner understanding what "no duplicates" means at the list level. Without it, the learner arrives at W4 without the vocabulary or intuition for `Nodup`, `dedup`, or the information-loss story. The plan explicitly marks this level as M17 (I) -- the **introduction** of `List.Nodup` -- meaning no other world introduces it.

**Where**: A new level should replace or supplement L07 (ListReverse). Ideally, the Nodup level comes before the boss and after the current L06 (ListAppend), since the plan places it at position 7. `List.reverse` could be folded into the boss or into the append level, or kept as a bonus level if the world grows. But Nodup must not be omitted.

**Effort**: High (adding a new level with substantive content).

**Recommend**: Yes. This is not optional -- it is a plan-critical introduction that downstream worlds depend on.

---

### 2. Every proof in the world is solved by `decide` or `simp` alone -- no genuine proof reasoning

**What**: All eight levels have proofs that reduce to a single tactic (`rfl`, `simp`, or `decide`). No level requires the learner to do multi-step reasoning, compose lemmas, or use `rw` with a list API lemma.

**Why**: This means the world teaches the learner to recognize list operations and press `decide`, but never teaches them to *reason* about lists. There is a qualitative difference between "Lean can compute this" and "I understand how this works." The plan's boss (L08) calls for combining `map`, `filter`, `length`, and membership -- the implemented boss combines `append`, `reverse`, and membership, and is solved by `decide`. The learner leaves the world having never used a list lemma like `List.length_append`, `List.mem_map`, or `List.length_map`. This is a proof-move gap: the world introduces no proof moves at all.

More concretely, this world should be teaching the learner how `simp` works with list-specific lemma families (e.g., `List.mem_cons`, `List.mem_append`) as a precursor to W6 where `simp` with finset lemma families becomes central. The plan marks `simp` as introduced in W2 for `decide`-type use, but list-specific `simp` usage would be a natural stepping stone.

**Where**: At minimum, one or two levels should require multi-step proofs. For example:
- A level proving `a in l1 ++ l2 -> a in l1 \/ a in l2` (membership in append) using `List.mem_append`.
- A level proving `(List.map f l).length = l.length` for a specific `f` and `l` using `List.length_map`.
- The boss should require composing at least two reasoning steps rather than being solvable by `decide`.

**Effort**: High (modifying multiple levels and the boss to include genuine proof steps).

**Recommend**: Yes. A world where every proof is `decide` does not teach proof moves.

---

### 3. Missing: a level on `List.head?` / `List.get?` / indexing -- the connection from lists to `Fin`

**What**: Lists have a natural connection to `Fin n` via indexing: `List.get l i` where `i : Fin l.length` retrieves the element at position `i`. This connection is never mentioned.

**Why**: This world follows W1 (What is `Fin n`?). The learner just learned about `Fin n` as `{ i : Nat // i < n }`. The insight that list indexing produces exactly a `Fin l.length` constraint is a natural reinforcement of `Fin`. It also foreshadows `Fin`-indexed functions (which are conceptually lists), connecting to W23 where matrices are defined as functions `Fin m -> Fin n -> alpha`.

A single level where the learner uses `List.get` with a `Fin` index would:
- Reinforce `Fin` from W1 (retrieval practice).
- Show why `Fin` matters as an index type (motivation for an otherwise abstract concept).
- Foreshadow the "functions on finite types" perspective that the course builds toward.

**Where**: After L03 (ListMem), before L04 (ListMap). This keeps the flow: constructors -> length -> membership -> indexing -> transformations.

**Effort**: Medium (adding one level).

**Recommend**: Yes. The `Fin`-indexing connection is too natural to omit given the course structure.

---

### 4. `List.reverse` is taught but has no connection to multisets or permutations

**What**: L07 introduces `List.reverse` as a standalone operation. The conclusion mentions that "reversing preserves membership but destroys ordering information" and previews multisets. But it never makes the concrete observation that `l` and `l.reverse` are permutations of each other -- i.e., `List.Perm l l.reverse` -- which is the exact concept W4 will formalize.

**Why**: This is a missed foreshadowing opportunity. The word "permutation" could be seeded here (vocabulary seeding for W4), and the learner could see informally that "same elements, different order" is a real equivalence relation. This would make W4.2 (`List.Perm` and multiset equality) feel like a formalization of something already understood, rather than a brand-new concept.

**Where**: The conclusion of L07 (ListReverse). Add one or two sentences: "In fact, `[1, 2, 3, 4]` and `[4, 3, 2, 1]` are *permutations* of each other -- they contain the same elements in a different order. In the next world, you will see that Lean formalizes this as `List.Perm`, and that two lists that are permutations of each other give rise to the same *multiset*."

**Effort**: Low (a sentence in a conclusion).

**Recommend**: Yes.

---

### 5. No level on `List.nil` / `List.cons` pattern matching -- the structural recursion angle

**What**: L01 shows that `[1, 2, 3] = 1 :: 2 :: 3 :: []` via `rfl`. But no level explores pattern matching on lists: given a list, destructure it into head and tail (or show it is nil). This is the fundamental proof move for lists.

**Why**: Lists are an inductive type. The learner will encounter induction on finsets in W10, and induction on natural numbers is part of the NNG4 baseline. But list induction / case splitting (the `cases` tactic on a `List`) is never shown. This is a proof-move gap: the learner learns to compute with lists but never to reason structurally about them.

A level that says "given `l : List Nat` and `l.length > 0`, show there exist `a` and `t` such that `l = a :: t`" would teach the learner to destructure a list. This is a natural use of `cases` (already in the NNG4 baseline) on a new type, which is valuable practice.

**Where**: After L01 (ListCons), as a follow-up that uses the constructors in the other direction: not building a list, but taking one apart.

**Effort**: Medium (adding one level).

**Recommend**: Consider. This is valuable but could make the world too large. If the Nodup level and indexing level are added, the world may already be at 10 levels, which is the upper bound for a lecture world in this course. This suggestion could be deferred to the boss or to a later world.

---

### 6. `List.map` level does not show that map preserves membership -- a derivable result left as a stated property

**What**: L04 introduces `List.map` and states in the introduction that `(List.map f l).length = l.length`. The conclusion states that map preserves length and order. But no level asks the learner to prove that `a in l -> f a in List.map f l` (membership is preserved under map). The only proof is `List.map (· * 2) [1, 2, 3] = [2, 4, 6]`, which is solved by `decide`.

**Why**: The membership-preservation property (`List.mem_map`) is directly relevant to W8 (Filter, image, and map), where `Finset.image` is the finset analogue. If the learner has already proved `a in l -> f a in List.map f l` for lists, then `mem_image` for finsets will feel like a natural generalization rather than a new concept. This is an example of a derivable result presented only as a remark when it should be an exercise.

**Where**: Modify L04 to ask the learner to prove `2 in [1, 2, 3] -> 4 in List.map (· * 2) [1, 2, 3]`, or better yet, add a follow-up level proving the general `List.mem_map` direction.

**Effort**: Medium (modifying one level or adding one).

**Recommend**: Yes. This is exactly the kind of derivable result the enrichment reviewer is designed to catch.

---

### 7. `List.filter` level uses `fun x => decide (x < 4)` -- an awkward encoding that obscures the concept

**What**: L05 writes the filter predicate as `fun x => decide (x < 4)` with a lengthy explanation about `Bool` vs `Prop` predicates. The introduction spends significant space on this distinction.

**Why**: This is a Lean-expression-layer burden that distracts from the mathematical content. The learner is supposed to be learning "filter keeps elements satisfying a predicate." Instead, they are confronting the `Bool`/`Prop` distinction, `decide` coercion, and `BEq`/`BLt` -- none of which are in the plan's coverage items for this level. The plan says "Filter a list by a predicate" (M16 (S)), not "learn about decidability coercion."

In mathlib/Lean 4, `List.filter (fun x => x < 4) [1, 2, 3, 4, 5]` works directly if the predicate is `DecidablePred`-compatible. Or `[1, 2, 3, 4, 5].filter (· < 4)` with the right coercion. The current encoding is more verbose than necessary and introduces concepts that are not in the plan.

**Where**: L05. Simplify the predicate to use a more natural encoding that does not require explaining `decide` as a `Prop -> Bool` coercion. If this requires a helper definition or a different predicate style, that is acceptable. The introduction should focus on "filter keeps elements that satisfy a condition."

**Effort**: Medium (rewriting one level).

**Recommend**: Yes. The current encoding violates the one-novelty-per-level rule: it introduces both `List.filter` (the intended lesson) and the `Prop`/`Bool` distinction (an unintended burden).

---

### 8. The boss (L08) does not exercise `List.map` or `List.filter` -- the plan says it should

**What**: The plan specifies W3.8 as "Combine `map`, `filter`, `length`, and membership in one proof." The implemented boss combines only `append`, `reverse`, and membership. `List.map` and `List.filter` are not used.

**Why**: The boss should be the integration point for the entire world. If the boss does not exercise `map` and `filter`, those operations get no retrieval practice within the world. The learner proves one fact about each, then never uses them again until W4 or W8. This weakens the world's coverage closure.

**Where**: L08. Redesign the boss to require at least three operations. For example: "Prove that `5 in (List.map (· + 1) (List.filter (fun x => decide (x > 2)) [1, 2, 3, 4])).reverse`" -- this requires understanding filter (keeps 3, 4), map (gives 4, 5), reverse (gives 5, 4), and membership (5 is in [5, 4]). Even if solved by `decide`, the introduction should walk through the reasoning so the learner sees the composition.

Better yet, if suggestion 2 is implemented (making proofs require reasoning, not just `decide`), the boss could require multi-step reasoning with list lemmas.

**Effort**: Medium (rewriting one level).

**Recommend**: Yes.

---

### 9. No transfer moment anywhere in the world

**What**: The plan specifies transfer as a key output. The world has "In plain language" sentences in several conclusions, but no level where the learner explicitly restates a list concept in ordinary mathematical language. There is no transfer level or transfer moment in the conclusion.

**Why**: The List/Multiset/Finset hierarchy is called out in the transfer plan (Section 8) as T8 (covered in W8_ex.7 and elsewhere). But this world is where the learner first encounters lists as Lean objects. A sentence in the boss conclusion connecting `List` to the mathematical notion of "sequence" is present ("When you write 'consider the sequence (a_1, ..., a_n)' in a paper proof, you are working with a list"), which is good. However, this could be strengthened by asking the learner to articulate the difference between a list (ordered, with duplicates) and a set (unordered, no duplicates) in their own words -- previewing the hierarchy story.

**Where**: The conclusion of L08 (Boss). Add a question or remark: "Before moving on, consider: what would change if we stopped caring about the order of elements? What if we also removed duplicates? These questions lead to the next two worlds."

**Effort**: Low (a paragraph in a conclusion).

**Recommend**: Consider. The existing transfer text in the boss conclusion is adequate, but the prompt toward W4's hierarchy story could be stronger.

---

### 10. `List.append` associativity is mentioned but never proved or used

**What**: L06 lists `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)` as a key property in the introduction but never asks the learner to prove it or use it.

**Why**: Associativity of append is the simplest structural lemma about lists that the learner could prove (or see proved) using list induction -- or at least by `simp`. It would be a natural place to show that lists have algebraic structure, connecting forward to the algebraic structures course (Course 4 in the catalog). Even on concrete lists, showing that `([1, 2] ++ [3]) ++ [4, 5] = [1, 2] ++ ([3] ++ [4, 5])` and verifying both sides equal `[1, 2, 3, 4, 5]` would make the property tangible.

**Where**: L06 (ListAppend) or a new follow-up level.

**Effort**: Low (modifying L06 to change the goal) or Medium (adding a level).

**Recommend**: Consider. If the world is already growing due to the Nodup and indexing additions, this can stay as a remark in the introduction.

---

## Overall impression

The world does several things well. The introductions are clear and well-written, consistently providing the mathematical definition, concrete examples, and "in plain language" summaries. The progression from constructors to properties to operations to boss is logical. The conclusions reliably foreshadow later worlds (map -> image, filter -> finset filter, reverse -> multisets), which is good cross-world seeding. The writing tone is appropriate for the learner profile.

The single most important improvement is addressing the combination of two problems: (1) the missing `List.Nodup` level, which is load-bearing for the course's hierarchy story in W4, and (2) the fact that every proof in the world is trivially solved by `decide` or `simp`, meaning the learner exits the world having never composed a proof step with a list API lemma. These two problems together mean the world is functioning as a "tour of list operations" rather than as a teaching world. The learner reads about list operations and presses `decide` to confirm concrete computations, but never reasons about lists -- and misses the key concept (`Nodup`) that makes the next world's story work.
