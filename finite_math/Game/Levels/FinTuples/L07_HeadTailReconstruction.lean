import Game.Metadata

World "FinTuples"
Level 7

Title "Head-Tail Reconstruction"

Introduction "
# Every Tuple = Head + Tail

You've seen that `Fin.cons` prepends and `Fin.tail` drops.
The fundamental identity connecting them is:

$$\\texttt{Fin.cons}\\;(f\\;0)\\;(\\texttt{Fin.tail}\\;f) = f$$

In words: if you take the head of `f` (which is `f 0`) and
prepend it to the tail of `f` (which is `Fin.tail f`), you
get back `f` itself.

This is **`Fin.cons_self_tail`**: `Fin.cons (f 0) (Fin.tail f) = f`.

This identity says that `cons` and `(head, tail)` are inverse
operations. Every tuple is completely determined by its head
and its tail.

In mathematics: if $v = (v_0, v_1, \\ldots, v_{n-1})$, then
$v = v_0 :: (v_1, \\ldots, v_{n-1})$ where $::$ is prepending.

**Your task**: Prove this identity.
"

/-- Every tuple equals its head prepended to its tail. -/
Statement (f : Fin 3 → ℕ) :
    (Fin.cons (f 0) (Fin.tail f) : Fin 3 → ℕ) = f := by
  Hint "The theorem `Fin.cons_self_tail f` states exactly this:
  `Fin.cons (f 0) (Fin.tail f) = f`.
  Use `exact Fin.cons_self_tail f`."
  exact Fin.cons_self_tail f

Conclusion "
`Fin.cons_self_tail` is the key structural fact about tuples.
It says:

> Decomposing a tuple into head + tail and reassembling gives
> back the original tuple.

This is the *extensionality principle* for tuples: two functions
`Fin (n+1) -> alpha` are equal when they agree on all inputs.
You'll see this principle again for finsets — two finsets are equal
when they have the same members.

But is this a genuine round-trip? You've shown that decomposing
and reassembling recovers the original. In the next level, you'll
prove the reverse: assembling and then decomposing also recovers
the original components. Together, these make `Fin.cons` and
`(head, tail)` a proper bijection.
"

/-- `Fin.cons_self_tail f` states that
`Fin.cons (f 0) (Fin.tail f) = f`.

Every tuple equals its head prepended to its tail.

## Syntax
```
exact Fin.cons_self_tail f  -- proves cons (f 0) (tail f) = f
```

## When to use it
When you need to decompose a tuple into its first element
and the remaining elements.
-/
TheoremDoc Fin.cons_self_tail as "Fin.cons_self_tail" in "Fin"

NewTheorem Fin.cons_self_tail

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
