import Game.Metadata

World "MeetFin"
Level 20

Title "Using Fin as an Index"

Introduction "
# Fin in Action: Indexing Concrete Data

So far, `Fin` has been an abstract mathematical object. But `Fin n`
exists to **index things** — vector entries, polygon vertices, tuple
positions.

A function `Fin n → α` is essentially an `n`-element tuple: it assigns
a value of type `α` to each index `0, 1, ..., n-1`. You'll meet tuples
formally in the FinTuples world, but let's preview the idea.

**Key fact**: A function on `Fin 3` is completely determined by its
three values — `f 0`, `f 1`, and `f 2`. If two functions agree on
these three inputs, they agree everywhere. This is because `Fin 3`
has exactly three elements (as you proved in Level 18).

**Your task**: Prove that two functions `f g : Fin 3 → ℕ` are
equal on all inputs if they agree at positions 0, 1, and 2.

This requires case analysis: for each possible input `i : Fin 3`,
determine which of the three hypotheses closes the goal.
"

/-- A function on Fin 3 is determined by its three values. -/
Statement (f g : Fin 3 → ℕ) (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (h2 : f 2 = g 2) : ∀ i : Fin 3, f i = g i := by
  Hint "Start by introducing `i`, then destructure it:
  `intro i` then `cases i with | mk v hlt`"
  intro i
  Hint (hidden := true) "`cases i with | mk v hlt`"
  cases i with
  | mk v hlt =>
    Hint "Case-split on `v` to determine which position `i` is at.
    For each valid case (0, 1, 2), one of the three hypotheses
    closes the goal."
    cases v with
    | zero =>
      Hint "Here `i` is at position 0 (value `v = 0`).
      One of the three hypotheses `h0`, `h1`, `h2` matches.
      Use `exact h0`."
      exact h0
    | succ n =>
      Hint (hidden := true) "Case-split on `n`."
      cases n with
      | zero =>
        Hint (hidden := true) "Here `i` is at position 1. `exact h1` closes the goal."
        exact h1
      | succ m =>
        Hint (hidden := true) "Case-split on `m`."
        cases m with
        | zero =>
          Hint (hidden := true) "Here `i` is at position 2. `exact h2` closes the goal."
          exact h2
        | succ k =>
          Hint (hidden := true) "Impossible case: `exact absurd hlt (by omega)`."
          exact absurd hlt (by omega)

Conclusion "
This is the fundamental property of `Fin n` as an index type: since
`Fin n` has exactly `n` elements, any predicate on `Fin n` can be
verified by checking each element. A function `Fin n → α` is
determined by `n` values, and two such functions agree if and only
if they agree on all `n` inputs.

This is how `Fin n` connects to the concept of an **n-tuple**: the
function `f : Fin 3 → ℕ` is just the triple `(f 0, f 1, f 2)`. Two
triples are equal when they agree position by position. You'll
formalize this connection in the FinTuples world.

In the next level, you'll learn to prove that two `Fin` elements
are *not* equal — the inequality pattern.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Fin.forall_fin_two
