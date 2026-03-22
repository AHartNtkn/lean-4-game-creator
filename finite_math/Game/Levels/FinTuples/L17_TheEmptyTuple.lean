import Game.Metadata

World "FinTuples"
Level 17

Title "The Empty Tuple"

Introduction "
# There Is Only One Empty Tuple

What is `Fin 0 → ℕ`? It's a function from the *empty* type
`Fin 0` — a type with no elements.

Since there are no inputs, there are no choices to make: the
function has nothing to return. This means there is exactly
**one** function `Fin 0 → ℕ` (the empty function).

In tuple language: there is exactly one 0-tuple.

This is the tuple base case — analogous to the empty list `[]`.
Every inductive argument about tuples starts here.

The fact that `Fin 0` is empty also means something powerful:
*any* statement about all elements of `Fin 0` is vacuously true.
In Lean, `Fin.elim0 i` proves anything when `i : Fin 0`, because
no such `i` can ever exist.

**Your task**: Prove that any two functions `Fin 0 → ℕ` are equal.
Use `ext i` to introduce the index, then `exact Fin.elim0 i`
to eliminate the impossible case.
"

/-- Any two functions from Fin 0 are equal. -/
Statement (f g : Fin 0 → ℕ) : f = g := by
  Hint "Use `ext i` to introduce an index `i : Fin 0`."
  ext i
  Hint "The goal is `f i = g i` where `i : Fin 0`. But `Fin 0`
  has no elements! Use `exact Fin.elim0 i` to eliminate the
  impossible case."
  exact Fin.elim0 i

Conclusion "
`Fin.elim0 i` works because `i : Fin 0` is a value from the
empty type — it can never actually exist. Lean lets you prove
*anything* from an impossible hypothesis, and `Fin.elim0` is the
standard way to do this for `Fin 0`.

This is the tuple analog of the fact that the empty product
equals 1: there's exactly one way to make zero choices.

In the mathematical literature, this is written as
$\\alpha^0 = 1$ — the set of functions from the empty set to
$\\alpha$ has exactly one element. You just proved the content
of this identity: any two functions `Fin 0 -> alpha` are equal,
so there is at most one, and the empty function exists trivially.
In the Fintype world, you will prove this formally as
`Fintype.card (Fin 0 -> alpha) = 1 = alpha^0`, making the
connection between empty tuples and the exponentiation rule
`alpha^0 = 1` completely explicit.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext Subsingleton.elim Unique.eq_default
