import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 7

Title "Pigeonhole for general n"

Introduction
"
# The general pigeonhole principle

In the previous level you proved pigeonhole for a specific case
(`Fin 4 → Fin 3`). Now prove it for **all** `n`:

> For any `n : ℕ`, no function `Fin (n + 1) → Fin n` is injective.

The proof is exactly the same pattern:
1. Assume injectivity.
2. Use `Fintype.card_le_of_injective` to get `n + 1 ≤ n`.
3. Derive a contradiction.

The only difference is that the cardinalities are now *symbolic*
(`n + 1` and `n` instead of `4` and `3`), but `omega` handles
the arithmetic just as well.

## Your task

Prove the general pigeonhole principle.
"

/-- For any `n`, no function from `Fin (n + 1)` to `Fin n` is injective.
This is the pigeonhole principle. -/
Statement pigeonhole (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ¬ Function.Injective f := by
  Hint "Start with `intro hinj` to assume injectivity."
  intro hinj
  Hint "Use `have h := Fintype.card_le_of_injective f hinj` to derive the
  cardinality bound."
  have h := Fintype.card_le_of_injective f hinj
  Hint "Now rewrite both cardinalities. Use
  `rw [Fintype.card_fin, Fintype.card_fin] at h`."
  Hint (hidden := true) "After rewriting, `h : n + 1 ≤ n`. Use `omega`
  to derive the contradiction."
  rw [Fintype.card_fin, Fintype.card_fin] at h
  omega

Conclusion
"
You proved the **general pigeonhole principle**: for any $n$, a function
from an $(n+1)$-element set to an $n$-element set cannot be injective.

## The pattern

The proof was identical to the specific case:

| Step | Specific (L06) | General (L07) |
|------|----------------|---------------|
| Assume | `hinj : Injective f` | Same |
| Bound | `4 ≤ 3` | `n + 1 ≤ n` |
| Contradiction | `omega` | `omega` |

This is a hallmark of good formal reasoning: the same proof structure
works for any `n`, not just for `n = 3`.

## Named result

This statement has been added to your theorem inventory as `pigeonhole`.
You can use it in later levels.

**In plain language**: \"If you place $n + 1$ objects into $n$ containers,
some container must hold at least two objects.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
