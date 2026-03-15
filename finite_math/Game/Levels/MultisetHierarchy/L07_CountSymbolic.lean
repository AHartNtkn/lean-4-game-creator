import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 7

Title "Counting symbolically"

Introduction
"
# Reasoning about count with rewriting

In Level 6, you proved `Multiset.count 1 ↑[1, 2, 1, 3] = 2` by `decide`.
That worked because the multiset was concrete. But what if you need to
reason about counting in a more general way?

## The recursive structure of count

Counting in a multiset built by `cons` follows two rules:

### `Multiset.count_cons_self`
```
Multiset.count_cons_self a s : (a ::ₘ s).count a = s.count a + 1
```
When you add `a` to a multiset and then count `a`, the count increases by 1.

### `Multiset.count_cons_of_ne`
```
Multiset.count_cons_of_ne (h : a ≠ b) : (b ::ₘ s).count a = s.count a
```
When you add a **different** element `b` and count `a`, the count does not change.

Here `::ₘ` is multiset cons: `a ::ₘ s` adds element `a` to multiset `s`.

## Your task

Starting from the multiset `{2, 3} = ↑[2, 3]`, prove that adding `1` to
the front gives a multiset where `count 1 = 1`.

The goal involves `(1 ::ₘ ↑[2, 3]).count 1`. Since we are counting `1`
and the element we added is `1`, use `Multiset.count_cons_self` to reduce
this to `(↑[2, 3]).count 1 + 1`. Then verify `(↑[2, 3]).count 1 = 0` by
`decide`, which makes the whole expression equal to `1`.

**Strategy**:
1. `rw [Multiset.count_cons_self]` to peel off the matching cons
2. `decide` to finish the computation
"

/-- Counting `1` in the multiset `1 ::ₘ ↑[2, 3]` gives `1`. -/
Statement : Multiset.count 1 (1 ::ₘ (↑([2, 3] : List Nat) : Multiset Nat)) = 1 := by
  Hint "The goal is `(1 ::ₘ ↑[2, 3]).count 1 = 1`. You are counting `1` in a
  multiset whose head is also `1`. Which count lemma handles the case where the
  element being counted matches the head?"
  Hint (hidden := true) "Use `rw [Multiset.count_cons_self]`. This peels off the
  matching cons, giving `(↑[2, 3]).count 1 + 1 = 1`."
  rw [Multiset.count_cons_self]
  Hint "The goal is now `(↑[2, 3]).count 1 + 1 = 1`. Since `1` does not appear
  in `[2, 3]`, the count is `0`, so this becomes `0 + 1 = 1`. Try `decide`."
  decide

Conclusion
"
You just proved a counting result **symbolically**: instead of letting `decide`
evaluate the entire expression at once, you first used `count_cons_self` to
extract the structural fact (\"adding 1 increases the count of 1 by 1\"), then
computed the remaining piece.

This is the difference between **computational** and **symbolic** reasoning:
- **Computational**: `decide` evaluates the whole expression. Works for concrete
  data but gives no insight.
- **Symbolic**: `rw [count_cons_self]` reveals the structure. Works for
  general arguments and teaches transferable reasoning.

The two count lemmas form a recursive recipe:
- `count_cons_self`: counting `a` when the head is `a` → add 1
- `count_cons_of_ne`: counting `a` when the head is not `a` → unchanged

Together, they describe how `count` processes a multiset element by element --
just like `List.mem_cons` describes how membership processes a list.

**Why did `decide` work at the end?** After `rw [count_cons_self]`, the goal
became `(↑[2, 3]).count 1 + 1 = 1`. Lean can compute `(↑[2, 3]).count 1 = 0`
definitionally, reducing the goal to `0 + 1 = 1`, which is also definitional.
So `decide` (or even `rfl`) closes it. The symbolic step was the rewrite;
the final computation is just cleanup.

**In plain language**: \"To count how many red marbles are in a bag, look at
each marble: if it is red, add one to the tally; if not, skip it.\"
"

/-- `Multiset.count_cons_self a s` states that `(a ::ₘ s).count a = s.count a + 1`.
Adding an element to a multiset increases its count by 1.

Use `rw [Multiset.count_cons_self]` to simplify `count` when the element being
counted matches the head of the multiset. -/
TheoremDoc Multiset.count_cons_self as "Multiset.count_cons_self" in "Multiset"

/-- `Multiset.count_cons_of_ne` states that when `a ≠ b`,
`(b ::ₘ s).count a = s.count a`. Adding a different element does not change
the count.

Use `rw [Multiset.count_cons_of_ne h]` (where `h : a ≠ b`) to simplify `count`
when the element being counted differs from the head. -/
TheoremDoc Multiset.count_cons_of_ne as "Multiset.count_cons_of_ne" in "Multiset"

NewTheorem Multiset.count_cons_self Multiset.count_cons_of_ne
DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
