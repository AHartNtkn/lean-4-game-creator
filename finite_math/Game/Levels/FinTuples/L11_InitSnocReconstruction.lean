import Game.Metadata

World "FinTuples"
Level 11

Title "Init-Snoc Reconstruction"

Introduction "
# Every Tuple = Init Snoc'd with Last

You know that every tuple equals its head prepended to its tail:

$$\\texttt{Fin.cons}\\;(f\\;0)\\;(\\texttt{Fin.tail}\\;f) = f \\quad (\\texttt{Fin.cons\\_self\\_tail})$$

The dual identity is:

$$\\texttt{vecSnoc}\\;(\\texttt{Fin.init}\\;f)\\;(f\\;(\\texttt{Fin.last}\\;n)) = f \\quad (\\texttt{vecSnoc\\_self\\_init})$$

In words: taking all elements except the last (init), then
appending the last element (snoc), recovers the original tuple.

The cons/snoc duality is now complete:

| Build from | Decompose into | Reconstruct with |
|---|---|---|
| Front (`Fin.cons`) | head (`f 0`) + tail (`Fin.tail f`) | `Fin.cons_self_tail` |
| Back (`vecSnoc`) | init (`Fin.init f`) + last (`f (Fin.last n)`) | `vecSnoc_self_init` |

**Your task**: Prove the init-snoc reconstruction identity.
"

/-- Every tuple equals its init snoc'd with its last element. -/
Statement (f : Fin 3 → ℕ) :
    vecSnoc (Fin.init f) (f (Fin.last 2)) = f := by
  Hint "The theorem `vecSnoc_self_init f` states exactly this:
  `vecSnoc (Fin.init f) (f (Fin.last n)) = f`.
  Use `exact vecSnoc_self_init f`."
  exact vecSnoc_self_init f

Conclusion "
The cons/snoc duality is now complete. Every tuple can be
decomposed from either end:

**From the front**: `f = Fin.cons (f 0) (Fin.tail f)`
**From the back**: `f = vecSnoc (Fin.init f) (f (Fin.last n))`

Both decompositions are inverse operations: decomposing and
reassembling always recovers the original tuple.

This is the tuple analog of a bidirectional linked list — you
can traverse from the front or the back and reconstruct the
whole sequence either way.
"

NewTheorem vecSnoc_self_init

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
