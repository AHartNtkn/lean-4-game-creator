# W17 Factorials — Enrichment Review (Round 1)

## Ranked suggestions

### 1. The descFactorial unfolding direction is mathematically backward — fix L04's hint narrative

**What**: L04's hint tells the learner that `Nat.descFactorial_succ` applied to `descFactorial 5 3` gives `(5 - 2) * descFactorial 5 2 = 3 * descFactorial 5 2`, but the mathematical narrative in the introduction says descending factorials are "n(n-1)(n-2)...(n-k+1)", which goes *top-down* (5, 4, 3). The recursion actually peels off factors from the *bottom* (3, then 4, then 5), producing `3 * 4 * 5 * 1` rather than `5 * 4 * 3 * 1`. The conclusion's displayed computation confirms this bottom-up order but does not explicitly acknowledge the mismatch with the standard mathematical presentation. This is a genuine pedagogical confusion point.

**Why**: A learner who reads "n(n-1)(n-2)..." and then sees the recursion produce factors in the opposite order (3, then 4, then 5) will be confused about whether the definition matches the standard one. This is exactly the kind of "why does this look different?" moment that should be addressed, not left implicit.

**Where**: L04 introduction and conclusion.

**Effort**: Low — add 2-3 sentences to the conclusion explaining that the recursion peels off the *smallest* factor first (because it unfolds `k+1` to `k`), which produces the same product in reverse order.

**Recommend**: Yes

---

### 2. Missing level: `0! = 1` is never proved or justified — only used

**What**: The world uses `Nat.factorial_zero` as a rewrite rule from L01 onward, but never pauses to discuss *why* `0! = 1`. This is one of the most frequently asked questions in combinatorics ("why is the factorial of zero equal to one?"), and the empty-product argument is a beautiful piece of mathematics that connects directly to L03's big-product theme.

**Why**: The TheoremDoc for `factorial_zero` says "by convention and by the empty-product principle" but never unpacks what the empty-product principle is. Since L03 explicitly shows `n! = prod i in range n, (i+1)`, this is the perfect place to instantiate n=0 and observe that the empty product is 1, giving a *derivation* of `0! = 1` from the product formula rather than treating it as a mysterious convention. This turns a fact-presented-as-axiom into a derived result.

**Where**: Best as an explicit remark in L03's conclusion (after the learner has seen the product connection), or as a short new level between L02 and L03 that asks the learner to prove `prod i in range 0, (i+1) = 1` using `prod_range_zero`.

**Effort**: Low (remark in L03 conclusion) or Medium (new level).

**Recommend**: Yes

---

### 3. Missing: `descFactorial` and `choose` connection is never mentioned

**What**: The descending factorial is intimately connected to binomial coefficients: `choose n k = descFactorial n k / factorial k`. The world introduces `descFactorial` but never mentions this connection, even though W18 (Binomial coefficients) is the very next lecture world.

**Why**: This is a major cross-world foreshadowing opportunity. The learner invests effort understanding `descFactorial` without knowing *why* it matters beyond counting permutations. A sentence in L04's conclusion or L05's conclusion saying "In the next world, you will see that `Nat.choose n k = n.descFactorial k / k!` — the descending factorial counts ordered selections, and dividing by `k!` forgets the ordering" would give the learner a reason to remember descFactorial.

**Where**: L04 or L05 conclusion.

**Effort**: Low — one or two sentences of foreshadowing text.

**Recommend**: Yes

---

### 4. L02 proves a trivial restatement instead of a genuinely algebraic identity

**What**: L02 asks the learner to prove `n! * (n+1) = (n+1)!`, which is literally `factorial_succ` with `mul_comm`. This is mechanical rather than algebraic. A better level would ask something that genuinely uses `factorial_succ` as a tool — for example, proving `(n+2)! = (n+2) * (n+1) * n!` (two-step unfolding) or proving `n! ∣ (n+1)!` (factorial divisibility).

**Why**: L02's stated lesson is "factorial recursion as an algebraic identity," but the proof is just `rw [factorial_succ]; rw [mul_comm]`. The learner practices no new skill beyond what L01 taught. A two-step unfolding or a divisibility result would actually require multi-step reasoning and teach something new.

**Where**: L02 (replace or add a follow-up).

**Effort**: Medium — rewriting the level statement and proof.

**Recommend**: Consider

---

### 5. L03 verifies the product identity for n=4 but the boss proves it generally — the concrete case teaches nothing the boss doesn't

**What**: L03 asks the learner to verify `prod i in range 4, (i+1) = 4!` by unfolding both sides numerically. L07 (boss) proves the general statement by induction. L03 exists as a "concrete verification before the general proof" level. But the concrete verification teaches a different strategy (unfold everything to numbers, then `ring`) than the induction proof, so L03 does not actually prepare the learner for L07.

**Why**: The gap between "unfold everything to numbers" (L03) and "prove by induction" (L07) is large. A better intermediate step would be to have L03 prove the n=1 or n=2 case of the induction argument (i.e., using the same `factorial_succ` / `prod_range_succ` / `ih` / `mul_comm` structure that L07 uses, but on a concrete step). This would make L03 a genuine rehearsal for the boss rather than a disconnected computation.

**Where**: L03 (modify the proof strategy, or add a new level between L03 and L07 that does one inductive step concretely).

**Effort**: Medium.

**Recommend**: Consider

---

### 6. The "descending factorial" narrative conflates two different recursion lemmas without naming the proof move

**What**: L04 uses `descFactorial_succ` (subtractive recursion) and L05 uses `succ_descFactorial_succ` (successor recursion). These are two genuinely different ways to recurse on descending factorials, but the world never explicitly names the pattern: "When proving facts about `descFactorial n k` by induction on *k*, use `descFactorial_succ`. When proving facts by induction on *n* and *k* simultaneously (both going up), use `succ_descFactorial_succ`." This is an unnamed strategy.

**Why**: The learner will encounter this choice again (e.g., when working with binomial coefficients, which also have both subtractive and successor recursions). Naming the strategy here — "choose the recursion that matches your induction variable" — pays dividends later.

**Where**: L05 introduction or conclusion (after the learner has used both).

**Effort**: Low — add a paragraph naming the strategy.

**Recommend**: Yes

---

### 7. L06 does not connect back to L04/L05 — missed opportunity for `descFactorial` in permutation counting

**What**: L06 proves `card (Perm (Fin 3)) = 6` using `card_perm` and `card_fin`, which goes through `factorial`. But the descending factorial directly counts *k*-permutations of *n* objects. The world never shows this: there is no level asking "how many ways can you choose and arrange 3 objects from 5?", which would be `descFactorial 5 3 = 60` with a combinatorial interpretation. L04 computes `descFactorial 5 3 = 60` but only as a numerical exercise, not as a counting result.

**Why**: The plan's coverage item for L06 is "M36 (preview)" — previewing permutation counting. But the preview only covers full permutations (`n!`). Partial permutations (`n^{underline{k}}`), which are exactly what `descFactorial` counts, are introduced in L04's text but never connected to actual counting. Adding even a sentence to L06's conclusion saying "If you wanted to count the number of ways to arrange only 3 of the 5 objects — a 3-permutation of 5 — that's exactly `descFactorial 5 3 = 60` from Level 4" would close this loop.

**Where**: L06 conclusion.

**Effort**: Low — a few sentences connecting L04's computation to L06's counting interpretation.

**Recommend**: Yes

---

### 8. No level addresses the non-obvious fact that `descFactorial n k = 0` when `k > n`

**What**: When `k > n`, the descending factorial hits zero in the product (specifically, at the factor `n - k` where subtraction wraps to 0 in `Nat`). This is mathematically significant: you cannot arrange more objects than you have. But the world never shows this. A quick computation like `descFactorial 3 5 = 0` would demonstrate the boundary behavior and prevent the misconception that `descFactorial` always gives a positive number.

**Why**: This is a natural "what if?" moment. The learner computed `descFactorial 5 3 = 60` in L04. What about `descFactorial 3 5`? Showing that it equals 0 — and explaining *why* (the Nat subtraction `3 - 3 = 0` produces a zero factor) — is a misconception-preventing level. It also foreshadows the fact that `choose n k = 0` when `k > n` (W18 L03).

**Where**: New level after L04, or a remark in L04's conclusion.

**Effort**: Low (remark) or Medium (new level).

**Recommend**: Yes

---

### 9. L01 proof is purely mechanical — no mathematical reasoning required

**What**: L01 asks the learner to compute `5! = 120` by applying `factorial_succ` five times and `factorial_zero` once. This is pure rewriting with no decision-making. The learner does not need to understand what a factorial is to complete it.

**Why**: The first level of a world sets the tone. A computation level is fine for grounding, but the current version requires zero thought beyond "keep rewriting." Consider having the learner also state *what* the intermediate values are (e.g., a `have` step: `have h4 : Nat.factorial 4 = 24 := by ...`), which would force engagement with the actual numbers rather than mindless rewriting. Alternatively, the final goal after all rewrites could require the learner to observe that `5 * 4 * 3 * 2 * 1 * 1 = 120` and use `ring` or `norm_num`, which would at least confirm they understand the product.

**Where**: L01.

**Effort**: Medium — restructuring the proof.

**Recommend**: Consider

---

### 10. The world conclusion (L07) does not preview transfer to paper-proof writing for induction

**What**: L07's conclusion has a "Transfer moment" that shows the paper proof, which is good. But it does not ask the learner to reflect on the *structure* of induction proofs they have now done multiple times (L05 and L07 in this world alone, plus many in earlier worlds). A sentence like "Notice that every induction proof in this world follows the same three-act structure: base case, rewrite-to-match, apply-IH. This is the canonical shape of a proof by induction on a recursively-defined function." would name a pattern the learner has used repeatedly.

**Where**: L07 conclusion.

**Effort**: Low — a few sentences.

**Recommend**: Consider

---

## Overall impression

The Factorials world is well-structured with a clear arc from definition (L01-L02) through connection to big products (L03) to descending factorials (L04-L05) to counting (L06) and back to integration (L07). The boss level is genuine — it requires putting together tools from across the world and from earlier worlds. The Transfer moments in L03, L05, and L07 are a strength that should be preserved.

The single most important improvement is **suggestion #6 (naming the "choose the recursion that matches your induction variable" strategy)** combined with **suggestion #7 (connecting descFactorial back to counting in L06)**. Together, these would close the biggest pedagogical gap in the world: the learner currently invests significant effort learning descending factorials (L04-L05) without understanding *why* they matter combinatorially or *how* to choose between the two recursion lemmas. Fixing this transforms L04-L06 from a sequence of disconnected exercises into a coherent argument about counting with structure.
