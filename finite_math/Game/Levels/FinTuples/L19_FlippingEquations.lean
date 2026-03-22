import Game.Metadata

World "FinTuples"
Level 19

Title "Flipping Equations"

Introduction "
# The .symm Suffix

Sometimes you have an equation pointing the wrong way. If
`h : a = b`, you need `b = a`. The suffix **`.symm`** flips
an equation:

> If `h : a = b`, then `h.symm : b = a`.

This works on any equation — it's the symmetry of equality.

**Why does direction matter?** In Lean, `rw [h]` is a
**directional** operation: if `h : a = b`, it replaces `a` with
`b` (left-to-right), never the reverse. So even though `a = b`
and `b = a` are logically equivalent, `rw [h]` and `rw [h.symm]`
do different things. When a lemma gives you `a = b` but you need
to replace `b` with `a`, you must flip the equation with `.symm`
before rewriting.

You already know two reconstruction identities:
- `Fin.cons_self_tail f : Fin.cons (f 0) (Fin.tail f) = f`
- `vecSnoc_self_init f : vecSnoc (Fin.init f) (f (Fin.last n)) = f`

Both say 'reconstructed = original'. But often you need the
reverse direction: 'original = reconstructed'. That's where
`.symm` comes in:
- `(Fin.cons_self_tail f).symm : f = Fin.cons (f 0) (Fin.tail f)`
- `(vecSnoc_self_init f).symm : f = vecSnoc (Fin.init f) (f (Fin.last n))`

**Your task**: Prove both reversed reconstruction identities.
"

/-- Flip both reconstruction identities. -/
Statement (f : Fin 3 → ℕ) :
    f = Fin.cons (f 0) (Fin.tail f) ∧
    f = vecSnoc (Fin.init f) (f (Fin.last 2)) := by
  Hint "Use `constructor` to split the conjunction."
  constructor
  · Hint "The goal is `f = Fin.cons (f 0) (Fin.tail f)`.
    You know `Fin.cons_self_tail f : Fin.cons (f 0) (Fin.tail f) = f`.
    Flip it with `.symm`: `exact (Fin.cons_self_tail f).symm`."
    exact (Fin.cons_self_tail f).symm
  · Hint "The goal is `f = vecSnoc (Fin.init f) (f (Fin.last 2))`.
    Similarly: `exact (vecSnoc_self_init f).symm`."
    exact (vecSnoc_self_init f).symm

Conclusion "
The `.symm` suffix is a general-purpose tool:

- `h.symm` flips any equation `h : a = b` to `b = a`
- `(theorem_name args).symm` flips a theorem's conclusion

You'll use `.symm` constantly — whenever a lemma gives you
`a = b` but you need `b = a`.

In the next level, you'll combine `.symm` with `rw ... at` to
build a powerful proof strategy: start with a flipped
reconstruction identity, substitute known values using `rw`,
and close the goal.
"

/-- `symm` flips an equation or equivalence.

## As a term suffix (primary usage)
If `h : a = b`, then `h.symm : b = a`.
If `h : P ↔ Q`, then `h.symm : Q ↔ P`.

This is the most common form — attach `.symm` to any proof
to flip its direction. Works with theorems too:
`(Fin.cons_self_tail f).symm` flips the conclusion.

## As a tactic
When the goal is `a = b`, the tactic `symm` changes it to `b = a`.
Useful when a lemma proves `b = a` and you want to match the
goal direction before using `exact`.

## When to use it
When you have an equation or lemma pointing the wrong way —
`a = b` when you need `b = a`.
-/
TacticDoc symm

NewTactic symm

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
