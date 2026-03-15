import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 3

Title "Filter the evens"

Introduction
"
# Filtering {1, 2, 3, 4, 5} by evenness

In the Filter, Image, and Map world, you learned that
`Finset.filter p s` keeps exactly those elements of `s` satisfying `p`.
The key lemma was:

```
Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a
```

## Your task

Prove that filtering {1, 2, 3, 4, 5} by the predicate \"is even\"
(`x % 2 = 0`) gives {2, 4}.

**Strategy**: Use `ext x` to reduce to membership. Then use
`Finset.mem_filter` on the left side and `Finset.mem_insert` /
`Finset.mem_singleton` on the right side, and let `omega` sort out
the arithmetic.
"

/-- The even elements of {1,2,3,4,5} are exactly {2, 4}. -/
Statement : Finset.filter (fun x => x % 2 = 0) ({1, 2, 3, 4, 5} : Finset Nat) =
    ({2, 4} : Finset Nat) := by
  Hint "To prove two finsets are equal, use `ext x` to reduce to
  membership: for each `x`, `x` belongs to the left side iff it belongs
  to the right side."
  Hint (hidden := true) "Use `ext x`."
  ext x
  Hint "Now you need to show:
  `x ∈ filter (fun x => x % 2 = 0) s ↔ x ∈ t` where `s` is our source
  finset and `t` is the target.

  Simplify both sides using the relevant membership lemmas, then let
  `omega` handle the arithmetic."
  Hint (hidden := true) "Use `simp only [Finset.mem_filter, Finset.mem_insert,
  Finset.mem_singleton]` then `omega`."
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  omega

Conclusion
"
The proof followed the `ext` + membership pattern:

1. **`ext x`**: reduce finset equality to membership equivalence.
2. **`simp only [...]`**: unfold `mem_filter`, `mem_insert`, `mem_singleton`
   on both sides.
3. **`omega`**: verify the arithmetic equivalence (which values of `x`
   satisfy `x ∈ {1,...,5} ∧ x % 2 = 0` iff `x ∈ {2, 4}`).

## What filtering does

Filtering {1, 2, 3, 4, 5} by evenness:
| Element | Even? | In result? |
|---------|-------|-----------|
| 1 | No  | No  |
| 2 | Yes | Yes |
| 3 | No  | No  |
| 4 | Yes | Yes |
| 5 | No  | No  |

Result: {2, 4}.

**In plain language**: \"The even numbers in {1, 2, 3, 4, 5} are 2 and 4.
We verify this by checking each element against the predicate.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
