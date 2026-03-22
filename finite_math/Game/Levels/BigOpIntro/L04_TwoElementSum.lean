import Game.Metadata

World "BigOpIntro"
Level 4

Title "A Two-Element Sum"

Introduction "
# Computing a Concrete Sum

Now put the pieces together: compute `∑ x ∈ s, f x` where `s` is a
two-element finset.

Remember that `{1, 2}` is `insert 1 {2}`. So after substituting `s`:
1. Use `sum_insert` to peel off `1` (after proving `1 ∉ {2}`)
2. Use `sum_singleton` to evaluate the remaining `∑ x ∈ {2}, f x`

The non-membership proof `1 ∉ {2}` is new here. The pattern:
- `rw [Finset.mem_singleton]` converts `1 ∉ {2}` to `¬(1 = 2)`
- `omega` closes the arithmetic contradiction

Use `have` to name the non-membership proof before applying
`sum_insert`.

**Your task**: Prove that `∑ x ∈ s, f x = f 1 + f 2` where `s` is
the two-element set.
"

/-- Unfolding a two-element sum with an abstract function. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ({1, 2} : Finset ℕ)) :
    ∑ x ∈ s, f x = f 1 + f 2 := by
  Hint "Start by substituting `s` with `rw [hs]`."
  rw [hs]
  Hint "Now the finset is concrete. Prove that 1 is not in the
  singleton containing 2, so you can use `sum_insert`. Use `have`
  to name the non-membership proof."
  Hint (hidden := true) "Use `have h : (1 : ℕ) ∉ (Finset.singleton 2) := by
  rw [Finset.mem_singleton]; omega`"
  have h : (1 : ℕ) ∉ ({2} : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega
  Hint "Now use `rw [Finset.sum_insert h]` to peel off the first
  element."
  rw [Finset.sum_insert h]
  Hint "Use `rw [Finset.sum_singleton]` to evaluate the singleton sum."
  rw [Finset.sum_singleton]

Conclusion "
You've computed your first concrete sum by unfolding:

$$\\sum_{x \\in \\{1, 2\\}} f(x) = f(1) + \\sum_{x \\in \\{2\\}} f(x) = f(1) + f(2)$$

The pattern for any concrete sum:
1. Prove non-membership: `have h : a ∉ s := by rw [...]; omega`
2. Peel: `rw [Finset.sum_insert h]`
3. Repeat until you reach a singleton
4. Close: `rw [Finset.sum_singleton]`

This is mechanical but important — it's how big-operator reasoning
reduces to ordinary arithmetic.

**Note**: Even if you found a shortcut for a two-element set, make sure
you understand the `sum_insert` + `sum_singleton` peel pattern — you'll
need it for larger sets where shortcuts don't work.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
