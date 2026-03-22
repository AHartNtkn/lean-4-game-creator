import Game.Metadata

World "BigOpIntro"
Level 5

Title "A Three-Element Sum"

Introduction "
# Unfolding a Larger Sum

Now compute `∑ x ∈ {10, 20, 30}, f x`. This requires **two** applications
of `sum_insert` before reaching a singleton.

The set `{10, 20, 30}` is `insert 10 (insert 20 {30})`, so:
1. Prove `10 ∉ {20, 30}` and peel with `sum_insert`
2. Prove `20 ∉ {30}` and peel again
3. Close with `sum_singleton`

For the first non-membership proof, `{20, 30}` is `insert 20 {30}`,
so use:
```
rw [Finset.mem_insert, Finset.mem_singleton]; omega
```

**Your task**: Prove that `∑ x ∈ {10, 20, 30}, f x = f 10 + f 20 + f 30`.
"

/-- Unfolding a three-element sum with an abstract function. -/
Statement (f : ℕ → ℕ) :
    ∑ x ∈ ({10, 20, 30} : Finset ℕ), f x = f 10 + f 20 + f 30 := by
  Hint "Start by proving 10 is not in the remaining set.
  Since the remaining set has two elements, you need both
  `mem_insert` and `mem_singleton` to unfold the membership test,
  then close with `omega`."
  have h1 : (10 : ℕ) ∉ ({20, 30} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_singleton]; omega
  Hint "Now peel with `rw [Finset.sum_insert h1]`."
  rw [Finset.sum_insert h1]
  Hint "Next, prove the second non-membership and peel again."
  Hint (hidden := true) "Prove 20 is not in the singleton containing 30:
  `have h2 : (20 : ℕ) ∉ (Finset.singleton 30) := by
  rw [Finset.mem_singleton]; omega`
  Then `rw [Finset.sum_insert h2]`."
  have h2 : (20 : ℕ) ∉ ({30} : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega
  rw [Finset.sum_insert h2]
  Hint "Finish with `rw [Finset.sum_singleton]` to evaluate the last
  singleton sum."
  rw [Finset.sum_singleton]
  Hint "The goal is now `f 10 + (f 20 + f 30) = f 10 + f 20 + f 30`.
  This is associativity of addition. Close with `omega`."
  omega

Conclusion "
The pattern scales: for any concrete finset, you peel elements
with `sum_insert` until you reach a singleton, then close with
`sum_singleton`. This is **sum peeling** — the big-operator
analogue of the **insert peeling** you used for finset membership
proofs. Both follow the same rhythm: prove non-membership, strip
off one layer, repeat.

Each peel requires a non-membership proof. For a set with `k` remaining
elements, the proof typically needs `k - 1` uses of `mem_insert` and one
`mem_singleton`, all closed by `omega`.

In plain math, you've shown:
$$\\sum_{x \\in \\{10, 20, 30\\}} f(x) = f(10) + f(20) + f(30)$$

This is tedious for large sets — which is exactly why automation
tactics like `simp` exist. But understanding the manual process is
essential: when automation fails or does something unexpected, this
is the mechanism underneath.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
