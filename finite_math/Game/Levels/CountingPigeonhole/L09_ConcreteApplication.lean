import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 9

Title "Six people, five rooms"

Introduction
"
# A concrete pigeonhole application

Here is a classic puzzle:

> **Six people check into a hotel with five rooms. Prove that at least
> two people must share a room.**

We model this as a function `assign : Fin 6 → Fin 5`, where
`assign i` is the room assigned to person `i`. The conclusion is
that two distinct people are assigned the same room:
`∃ p q, p ≠ q ∧ assign p = assign q`.

## Your task

Apply `Fintype.exists_ne_map_eq_of_card_lt` just as in the previous level.
The mathematical content is the same --- only the story is different.

This is the **transfer moment**: can you recognize pigeonhole in a
word problem and apply the same formal tool?
"

/-- If 6 people are assigned to 5 rooms, two people share a room. -/
Statement (assign : Fin 6 → Fin 5) :
    ∃ p q, p ≠ q ∧ assign p = assign q := by
  Hint "This is pigeonhole again: `|domain| = 6 > 5 = |codomain|`.
  Apply `Fintype.exists_ne_map_eq_of_card_lt` to the assignment function."
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint "Prove the cardinality condition: `Fintype.card (Fin 5) < Fintype.card (Fin 6)`.
  Rewrite with `Fintype.card_fin` and close with arithmetic."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_fin]` to
  get `5 < 6`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `5 < 6`. Use `omega` to close it."
  omega

Conclusion
"
The hotel puzzle is solved: with 6 people and only 5 rooms, two people
must share a room.

## Transfer: from Lean to mathematics

The formal proof was:
1. Model the room assignment as `assign : Fin 6 → Fin 5`.
2. Note `|Fin 6| = 6 > 5 = |Fin 5|`.
3. Apply `Fintype.exists_ne_map_eq_of_card_lt`.
4. Conclude: `∃ p q, p ≠ q ∧ assign p = assign q`.

In ordinary mathematical language, you would write:

> *Proof.* Let $f : \\{1, \\ldots, 6\\} \\to \\{1, \\ldots, 5\\}$ be the room
> assignment. Since the domain has more elements than the codomain,
> by the pigeonhole principle there exist distinct $p, q$ with
> $f(p) = f(q)$. That is, persons $p$ and $q$ share a room. $\\square$

**The Lean proof and the paper proof have the same structure.** The
only difference is that Lean verifies the cardinality comparison
mechanically, while in paper math you state it as obvious.
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
