import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 6

Title "Transfer: Read sigma notation"

Introduction
"
## Level 6: Transfer — Reading sigma notation

Here is a Lean sum expression:

```
∑ i ∈ Finset.range n, (i ^ 2 + 1)
```

Your task is to prove that this equals itself (so the Lean proof is
trivial). The real lesson is in the conclusion, where you will
translate this expression to standard mathematical notation.

Proving `X = X` is free — use `rfl`.
"

/-- A reflexive equality for a sum expression. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (i ^ 2 + 1) =
    ∑ i ∈ Finset.range n, (i ^ 2 + 1) := by
  Hint (hidden := true) "Both sides are identical. Use `rfl`."
  rfl

Conclusion
"
The proof was trivial — the real exercise is translation.

## The paper version

The Lean expression `∑ i ∈ Finset.range n, (i ^ 2 + 1)` corresponds
to the standard notation:

$$\\sum_{i=0}^{n-1} (i^2 + 1)$$

Note the key conventions:

| Lean | Paper |
|------|-------|
| `Finset.range n` | $i = 0, 1, \\ldots, n-1$ |
| `i ^ 2 + 1` | $i^2 + 1$ |
| `∑ i ∈ s, f i` | $\\sum_{i \\in S} f(i)$ |

**Caution**: `range n` runs from `0` to `n - 1`, not `1` to `n`.
This is a frequent source of off-by-one errors when translating
between Lean and paper.

**Transfer check**: You can now read a Lean `∑` expression and
write it in standard sigma notation. This retrieves T10.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
