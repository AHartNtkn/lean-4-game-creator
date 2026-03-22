import Game.Metadata

World "AbstractionLadder"
Level 3

Title "List Membership"

Introduction "
# Membership in Lists

Just like finsets have `Finset.mem_insert`, lists have `List.mem_cons`:

$$a \\in b :: l \\;\\longleftrightarrow\\; a = b \\;\\lor\\; a \\in l$$

In words: `a` belongs to the list `b :: l` if either `a` equals the
head `b`, or `a` is somewhere in the tail `l`.

The base case is: nothing belongs to the empty list (`a ∉ []`).

**Your task**: Prove that `2` belongs to the list `[1, 2, 3]`.

The strategy is the same membership-peeling move you learned for finsets:
1. `rw [List.mem_cons]` to convert `2 ∈ 1 :: [2, 3]` into `2 = 1 ∨ 2 ∈ [2, 3]`
2. Choose `right` (since `2 ≠ 1`)
3. Peel again and choose `left`
"

/-- 2 belongs to the list [1, 2, 3]. -/
Statement : (2 : ℕ) ∈ [1, 2, 3] := by
  Hint "The list `[1, 2, 3]` is `1 :: [2, 3]`. Use `rw [List.mem_cons]`
  to unfold the membership into a disjunction."
  rw [List.mem_cons]
  Hint "The goal is `2 = 1 ∨ 2 ∈ [2, 3]`. Since `2 ≠ 1`, choose the
  right branch."
  right
  Hint "Now prove `2 ∈ [2, 3]`. Peel again with `rw [List.mem_cons]`."
  rw [List.mem_cons]
  Hint "The goal is `2 = 2 ∨ 2 ∈ [3]`. The left branch is immediate."
  left
  Hint (hidden := true) "The goal is `2 = 2`. Close with `rfl`."
  rfl

Conclusion "
The membership proof pattern for lists is identical to finsets:
**peel and choose**. Use `List.mem_cons` to unfold one layer, then
`left`/`right` to navigate.

The key difference from finsets: in a list, the *position* where you
find the element matters for the proof (you need the right number of
peels), even though membership itself doesn't care about position.

**Reusable recipe**: `rw [List.mem_cons]` then `left`/`right`.
"

/-- `List.mem_cons` states that `a ∈ b :: l ↔ a = b ∨ a ∈ l`.

## Syntax
```
rw [List.mem_cons]
```

## When to use it
When proving or reasoning about membership in a cons'd list.
This is the list analogue of `Finset.mem_insert`.
-/
TheoremDoc List.mem_cons as "List.mem_cons" in "List"

TheoremTab "List"
NewTheorem List.mem_cons

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
