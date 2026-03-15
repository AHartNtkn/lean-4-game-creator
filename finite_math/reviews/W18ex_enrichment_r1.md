# W18_ex PascalsTriangle — Enrichment Review (Round 1)

**World**: PascalsTriangle (W18_ex, Example world, 6 levels)
**World promise**: The learner computes explicit rows of Pascal's triangle and sees the pattern before the general theory.
**Prerequisite**: W18 (Binomial coefficients and Pascal's rule)

---

## Ranked suggestions

### 1. Row 3 is conspicuously absent — the skip from Row 2 to Row 4 breaks the pattern-building narrative

**What**: Add a level computing Row 3 entries (specifically C(3,1) = 3 via Pascal's rule) between L03 (Row 2) and L04 (Row 4).

**Why**: The world promise is "the learner computes explicit rows of Pascal's triangle and sees the pattern emerge." Rows 0, 1, 2 are computed entry by entry, building momentum — then Row 3 is skipped entirely. The learner never sees the first row with two distinct interior values (3 and 3), never sees the first palindrome with length > 3, and never computes C(3,1) = C(2,0) + C(2,1) = 1 + 2 = 3, which is the first time Pascal's rule produces a value greater than 2. This is the most natural next computation in the sequence, and skipping it creates a gap in the pattern-recognition experience. The jump to Row 4 (which is used only for row-sum and symmetry, not for entry-by-entry computation) means the learner goes from computing individual entries to applying general theorems without ever doing the middle-difficulty computation.

**Where**: New level between L03 and L04.

**Effort**: Medium (new level, straightforward computation following the L02/L03 pattern).

**Recommend**: Yes.

---

### 2. L04 uses `Nat.sum_range_choose` to close the row-sum goal in one step — the learner does no actual computation

**What**: Restructure L04 so the learner first computes the row sum by expanding the `Finset.sum` over `range 5` into its five terms, evaluating each `Nat.choose 4 k` to a numeral, and then adding them up. The connection to `2^4` via `Nat.sum_range_choose` should come second — as a "now see why this equals 2^4" reflection, not as the entire proof.

**Why**: In an Example world, the point is computation, not theorem application. The current L04 teaches the learner to do `rw [Nat.sum_range_choose]; norm_num`, which is a two-step proof that invokes a powerful theorem and then computes. The learner never touches the individual entries of Row 4, never adds 1 + 4 + 6 + 4 + 1, and never experiences the row-sum identity as something you can *check by hand*. The conclusion text beautifully enumerates all the subsets of {a,b,c,d} — but the proof doesn't engage with that concreteness at all. This is a case where the proof and the pedagogy are misaligned: the conclusion tells the learner what they should have experienced, but the proof denied them the experience.

**Where**: L04 (restructure).

**Effort**: High (rethinking the proof structure, possibly splitting into two levels: one for computing the sum concretely, one for connecting to 2^n).

**Recommend**: Yes.

---

### 3. L05's proof requires an opaque `show (3 : N) = 4 - 1 from rfl` trick that undermines the pedagogical goal

**What**: Either (a) reformulate the goal so that `Nat.choose_symm` applies more naturally (e.g., state the goal as `Nat.choose 4 (4 - 1) = Nat.choose 4 1` and let the learner first verify `4 - 1 = 3`), or (b) use `norm_num` or `omega` to handle the arithmetic massage instead of the `show ... from rfl` construction, or (c) introduce the `show ... from rfl` pattern explicitly as a technique in the introduction text so it doesn't come as a surprise.

**Why**: The hint in L05 instructs the learner to type `rw [show (3 : N) = 4 - 1 from rfl, Nat.choose_symm (by omega : 1 <= 4)]`. This is the most syntactically complex tactic line in the entire world, appearing in what should be a conceptually simple level about symmetry. The `show ... from rfl` construction is never explained — it's a Lean-expression-layer skill that appears for the first time here with no setup. The learner is likely to be confused about what `show` does here (it's not the `show` tactic), why `from rfl` works, and why this elaborate construction is needed just to rewrite 3 as 4-1. This undermines the level's purpose: the symmetry of Pascal's triangle is a simple, beautiful idea, but the proof feels like a wrestling match with Lean syntax.

**Where**: L05 (modify proof approach or add explanation).

**Effort**: Medium.

**Recommend**: Yes.

---

### 4. The world skips Row 3 but also never computes any individual entry of Row 4 — the entries 4 and 6 are assumed, not derived

**What**: Add a level (or incorporate into the Row 3 suggestion above) where the learner computes C(4,2) = 6 via Pascal's rule: C(4,2) = C(3,1) + C(3,2) = 3 + 3 = 6. This is the first entry in Pascal's triangle that is "non-obvious" — you might not guess it's 6 without doing the recursion.

**Why**: The world's title is "Pascal's Triangle, Row by Row" and its promise is about computing rows. But the only entries actually computed by the learner are C(0,0), C(1,1), and C(2,1). After that, L04 uses a general theorem to verify the row *sum* without computing individual entries, and L05 proves two entries are *equal* without computing either one. The most interesting computation in the first five rows — the central entry C(4,2) = 6, which requires a two-step recursion through Row 3 — is never performed. If the Row 3 level is added (suggestion 1), then a follow-up computing C(4,2) from C(3,1) + C(3,2) would be the natural culmination of the computation sequence.

**Where**: New level between Row 3 and the current L04 (or incorporated into an expanded Row 4 section).

**Effort**: Medium (new level).

**Recommend**: Yes.

---

### 5. L06 (Transfer) is mathematically trivial and misses a transfer opportunity — the learner just applies two lemmas they already used in L01

**What**: Redesign L06 so the transfer task is genuinely about articulating the recursion, not about re-proving boundary identities. Options: (a) have the learner prove something about a *general* row (e.g., the endpoints of Row n are both 1, stated as `Nat.choose n 0 = 1 /\ Nat.choose n n = 1` with universally quantified n), which requires thinking about *why* the boundary lemmas hold in general; or (b) prove a concrete entry of Row 5 using Pascal's rule (e.g., C(5,1) = 5, requiring C(4,0) + C(4,1) = 1 + 4 = 5), which requires the learner to actually *use* the recursion one more time; or (c) prove both endpoints *and* an interior entry, making the level a genuine capstone.

**Why**: The current L06 asks the learner to prove `Nat.choose 5 0 = 1 /\ Nat.choose 5 5 = 1`. Both conjuncts are one-step rewrites using lemmas from L01 (`Nat.choose_zero_right`, `Nat.choose_self`). The introduction text says this is a "transfer moment" about understanding the recursion, but the proof doesn't involve the recursion at all — it only uses boundary conditions. The transfer text in the conclusion is excellent, but the proof task doesn't match it. A transfer level should ask the learner to demonstrate understanding that goes beyond mechanical lemma application.

**Where**: L06 (redesign).

**Effort**: Medium.

**Recommend**: Yes.

---

### 6. No level asks the learner to use Pascal's rule "forwards" — computing a Row-(n+1) entry from known Row-n entries

**What**: Ensure at least one level has the learner start with known values from a previous row and combine them to produce the next row's entry, i.e., "you know C(3,1) = 3 and C(3,2) = 3, so compute C(4,2)." Currently, L02 uses Pascal's rule to *decompose* C(1,1) into C(0,0) + C(0,1), and L03 decomposes C(2,1) into C(1,0) + C(1,1). The learner always starts with the target and breaks it down. The "forward" direction — "here are two known values, add them to get the next" — is the way you actually *build* the triangle on paper, and it's never exercised.

**Why**: Pascal's triangle on paper is constructed top-down: you write a row, then build the next row by adding adjacent pairs. The Lean proofs in this world all go in the opposite direction: start with the target entry and decompose it via `rw [Nat.choose_succ_succ]`. This is fine as a proof technique, but the *experience* of building the triangle is missing. One level that frames the task as "given these values from Row 3, compute this entry of Row 4" would give the learner the forward-construction experience. This connects to suggestion 4 (computing C(4,2)).

**Where**: Would be addressed by implementing suggestions 1 and 4.

**Effort**: Low (if suggestions 1/4 are implemented, just frame the introduction text appropriately).

**Recommend**: Consider.

---

### 7. The world never mentions the combinatorial interpretation — "C(n,k) counts k-element subsets" appears only in L04's conclusion table

**What**: Add a sentence in the L01 introduction (or L03 conclusion) explicitly connecting the computation to counting. For instance, in L01: "C(0,0) = 1 because there is exactly one way to choose 0 elements from an empty set: take nothing." In L03: "C(2,1) = 2 because there are exactly two ways to choose 1 element from {a, b}: take a or take b."

**Why**: The W18 lecture world includes a level (L07) on the combinatorial interpretation, so the learner has seen it. But this example world never explicitly connects the numbers being computed to the counting interpretation. L04's conclusion has a beautiful table of subsets of {a,b,c,d}, but this comes after the proof is done — it's retroactive. Threading the combinatorial meaning through the early levels would make the computations feel grounded rather than purely algebraic. The plan's coverage item E17 (concrete examples of binomial coefficients) is better served when examples carry combinatorial meaning.

**Where**: L01 introduction, L03 conclusion (text additions).

**Effort**: Low (a sentence or two in existing text).

**Recommend**: Yes.

---

### 8. The world never mentions that Row n has exactly n+1 entries — a basic structural fact about the triangle

**What**: Add a remark (in L01's introduction or a conclusion) noting that Row n contains exactly n+1 entries: the values C(n,0), C(n,1), ..., C(n,n). This is stated in L01's introduction ("Each row n contains the values C(n,0), C(n,1), ..., C(n,n)") but never explicitly connected to "Row n has n+1 entries." The connection is that k ranges from 0 to n, giving n+1 values.

**Why**: This is a minor point, but it's the kind of structural observation that helps learners understand the triangle's shape. When the learner sees Finset.range 5 in L04 (indexing the five entries of Row 4), the fact that Row 4 has 5 entries should feel like a known fact, not something to be inferred.

**Where**: L01 introduction (text addition).

**Effort**: Low.

**Recommend**: Consider.

---

### 9. Foreshadowing connection to the binomial theorem is absent

**What**: Add a sentence in the world conclusion (L06) noting that the entries of Row n are precisely the coefficients in the expansion of (a + b)^n. For example: "The entries 1, 4, 6, 4, 1 in Row 4 are exactly the coefficients in (a + b)^4 = a^4 + 4a^3b + 6a^2b^2 + 4ab^3 + b^4. This connection — binomial coefficients as coefficients — is the binomial theorem, which you will prove in the next world."

**Why**: The plan shows W19 is "Binomial identities and the binomial theorem," which immediately follows W18_ex. The connection between Pascal's triangle and the binomial theorem is one of the most important ideas in combinatorics, and seeding it here costs one sentence while giving the learner a reason to care about the next world. The conclusion of L06 currently says "the course continues with the binomial theorem and more advanced identities" but doesn't explain *why* the triangle is related to the binomial theorem.

**Where**: L06 conclusion (text addition).

**Effort**: Low.

**Recommend**: Yes.

---

### 10. `omega` is not in the DisabledTactic list — learner can close L05 (and possibly other levels) with `omega`

**What**: Verify whether `omega` can close any of the goals in this world (particularly L05 where the goal involves Nat.choose with concrete arguments) and add it to DisabledTactic if so.

**Why**: Past reviews have found that `omega` can sometimes close goals involving concrete natural number equalities. If `Nat.choose 4 1 = Nat.choose 4 3` reduces to `4 = 4` by computation, then `omega` might close it. This would bypass the lesson about `Nat.choose_symm`. The standard disabled set from the project's lessons learned includes `omega` on a per-level basis — it's worth checking here.

**Where**: All levels (DisabledTactic line).

**Effort**: Low.

**Recommend**: Consider.

---

## Overall impression

The world has a clear narrative arc and the text quality is high — the introductions motivate each computation well, the conclusions summarize what was learned, and the "triangle so far" diagrams in L02 and L03 are a nice visual thread. The L04 conclusion with the full enumeration of subsets of {a,b,c,d} is excellent pedagogical writing.

However, the **single most important improvement** is that the world doesn't live up to its own promise of row-by-row computation. The learner computes exactly three binomial coefficient values (C(0,0), C(1,1), C(2,1)) and then switches to applying general theorems (row sum, symmetry, boundary). Row 3 is skipped entirely, no entry of Row 4 is individually computed, and the transfer level re-proves something simpler than anything in the middle of the world. Adding Row 3, computing at least one entry of Row 4 concretely, and making the transfer level genuinely exercise the recursion (suggestions 1, 4, 5) would transform this from a world that *talks about* Pascal's triangle into one where the learner *builds* it.
