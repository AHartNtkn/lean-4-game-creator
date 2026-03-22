import Game.Metadata

World "CountingTypes"
Level 6

Title "Falling Factorial Identity"

Introduction "
# When k = n: Permutations

The falling factorial $n^{\\underline{k}}$ counts ordered selections
of `k` items from `n`. When `k = n`, you select ALL items —
that's a **permutation**, an ordering of every element.

The number of permutations of `n` items is $n!$ (factorial). So:

$$n^{\\underline{n}} = n!$$

For `n = 3`:
$3^{\\underline{3}} = 3 \\times 2 \\times 1 = 6 = 3!$

The proof technique is the same as the previous level — substitute,
unfold recursively, close with the base case. The lesson here is the
**mathematical identity**, not a new proof skill: when you select all
items, the falling factorial recovers the ordinary factorial.

**Your task**: Verify this by unfolding `n.descFactorial n` completely
(after substituting `n = 3`). This requires three `descFactorial_succ`
rewrites (one per factor from 3 down to 1) plus the
`descFactorial_zero` base case.
"

/-- The falling factorial 3^(3) = 3! = 6. -/
Statement (n : ℕ) (hn : n = 3) : n.descFactorial n = 6 := by
  Hint "The variable `n` blocks computation. Replace it with its
  concrete value first."
  Hint (hidden := true) "Try `rw [hn]`."
  rw [hn]
  Hint "The goal is `3.descFactorial 3 = 6`. Unfold the falling factorial
  one factor at a time — three unfolding steps to reach the base case."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "Keep unfolding — peel off the next factor."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "One more unfolding to reach the base case."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "Close the base case."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_zero]

Conclusion "
$$3^{\\underline{3}} = 3 \\times 2 \\times 1 = 6 = 3!$$

When `k = n`, you must place every item — that's a permutation. The
falling factorial recovers the ordinary factorial:

$$n^{\\underline{n}} = n!$$

In Lean, the theorem `Nat.descFactorial_self` expresses this directly,
but here you proved it from the recursive definition.

| Selection type | Count | Formula |
|---|---|---|
| All functions `Fin k → Fin n` | $n^k$ | `card_fun` |
| Injections `Fin k ↪ Fin n` | $n^{\\underline{k}}$ | `card_embedding_eq` |
| Permutations `Fin n ≃ Fin n` | $n!$ | `descFactorial_self` |

The falling factorial interpolates between functions ($n^k$, with
replacement) and permutations ($n!$, no replacement). When $k = n$,
every item must be used, so the falling factorial recovers the
factorial.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Keep descFactorial shortcuts disabled
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
