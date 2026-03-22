import Game.Metadata

World "MeetFin"
Level 8

Title "Transferring Bounds"

Introduction "
# Rewriting Through Fin Equality

In Level 7, you used `rw [Fin.ext_iff] at h` to convert a Fin
equality into a value equality, then closed with `omega`.

There's a more direct approach. Since `h : a = b` is an equality
of `Fin` elements, you can use `rw [h] at p` to replace `a` with
`b` directly in any hypothesis `p`. This turns
`p : a.val ≤ 2` into `p : b.val ≤ 2` — exactly the goal.

This is different from Level 7's technique:
- Level 7: `rw [Fin.ext_iff] at h` — converts the *equality* from
  Fin-level to value-level, then uses `omega`
- This level: `rw [h] at p` — rewrites a *different hypothesis*
  using the Fin equality directly

Both are useful. The first decomposes the equality; the second
propagates it.

**Your task**: Transfer a bound from `a` to `b`.
"

/-- Transfer a bound through a Fin equality by direct rewriting. -/
Statement (a b : Fin 5) (h : a = b) (p : a.val ≤ 2) : b.val ≤ 2 := by
  Hint "Use `rw [h] at p` to replace `a` with `b` in `{p}`.
  Since `{h}` says `a = b`, this turns `{p}` into `b.val ≤ 2`."
  rw [h] at p
  Hint "Now `{p}` says `b.val ≤ 2`, which is exactly the goal."
  exact p

Conclusion "
You've now seen two ways to use a Fin equality hypothesis:

| Technique | Syntax | Effect |
|---|---|---|
| Decompose the equality | `rw [Fin.ext_iff] at h` | Converts `h : a = b` to `h : a.val = b.val` |
| Propagate the equality | `rw [h] at p` | Replaces `a` with `b` in hypothesis `p` |

The first technique (Level 7) is useful when you need the *value*
equality for arithmetic. The second (this level) is useful when you
want to directly transform another hypothesis.

Both are instances of a general principle: `rw [...] at h` can
rewrite any hypothesis, not just the goal.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
