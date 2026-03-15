import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 6

Title "Transfer: Inclusion-exclusion"

Introduction
"
# Transfer: Inclusion-exclusion in words

The inclusion-exclusion principle says:

```
(s ∪ t).card + (s ∩ t).card = s.card + t.card
```

## Your task

Apply this principle to the finsets `s = {7, 8, 9}` and
`t = {9, 10, 11}`.

This is a one-lemma application. But the real lesson is in the
conclusion, where you will see the **paper version** of this
argument.
"

/-- Inclusion-exclusion for `{7, 8, 9}` and `{9, 10, 11}`. -/
Statement : (({7, 8, 9} : Finset Nat) ∪ {9, 10, 11}).card +
    (({7, 8, 9} : Finset Nat) ∩ {9, 10, 11}).card =
    ({7, 8, 9} : Finset Nat).card + ({9, 10, 11} : Finset Nat).card := by
  Hint (hidden := true) "Use `exact Finset.card_union_add_card_inter _ _`."
  exact Finset.card_union_add_card_inter _ _

Conclusion
"
You applied inclusion-exclusion. Now let us translate this to paper.

## The paper version

Let A = {7, 8, 9} and B = {9, 10, 11}.

- A ∪ B = {7, 8, 9, 10, 11}, so |A ∪ B| = 5.
- A ∩ B = {9}, so |A ∩ B| = 1.
- |A| = 3 and |B| = 3.
- Check: 5 + 1 = 6 = 3 + 3.

**In ordinary mathematical language**: \"The number of elements in
A ∪ B plus the number in A ∩ B equals |A| + |B|, because each element
of A ∪ B is counted once in |A| + |B| unless it is in the overlap,
in which case it is counted twice — once for A and once for B. The
extra count in |A ∩ B| compensates for this double-counting.\"

**Subtractive form**: The equivalent statement |A ∪ B| = |A| + |B| - |A ∩ B|
is often more familiar. In Lean, the additive form avoids natural-number
subtraction underflow.

**Transfer check**: You can now state and verify the inclusion-exclusion
principle in both Lean and paper notation. This retrieves T4.
"

DisabledTactic trivial decide native_decide aesop simp_all
