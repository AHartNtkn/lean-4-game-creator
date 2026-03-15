import GameServer.Commands
import Mathlib

World "CountingPset"
Level 5

Title "Transfer: Pigeonhole in words"

Introduction
"
# Transfer: Stating pigeonhole in paper language

Here is a concrete pigeonhole problem:

> **Eight students sign up for seven study groups. Prove that at least
> two students must be in the same group.**

We model this as a function `assign : Fin 8 → Fin 7`. The conclusion
is that two distinct students are assigned the same group.

The Lean proof is short. The real lesson is in the conclusion, where
you will see the **paper version** of this argument.
"

/-- If 8 students are assigned to 7 groups, two students share a group. -/
Statement (assign : Fin 8 → Fin 7) :
    ∃ s t, s ≠ t ∧ assign s = assign t := by
  Hint (hidden := true) "Apply `Fintype.exists_ne_map_eq_of_card_lt`,
  then prove `Fintype.card (Fin 7) < Fintype.card (Fin 8)` with
  `rw [Fintype.card_fin, Fintype.card_fin]` and `omega`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [Fintype.card_fin, Fintype.card_fin]
  omega

Conclusion
"
You proved that 8 students cannot all be in different groups when
there are only 7 groups.

## The paper proof

> *Let $f : \\{1, \\ldots, 8\\} \\to \\{1, \\ldots, 7\\}$ be the group
> assignment. Since $|\\text{domain}| = 8 > 7 = |\\text{codomain}|$,
> by the pigeonhole principle there exist distinct students $s \\neq t$
> with $f(s) = f(t)$. That is, students $s$ and $t$ are in the same
> group.* $\\square$

Notice how the Lean proof and the paper proof have the same logical
structure:
1. Model the situation as a function.
2. Compare domain and codomain sizes.
3. Apply pigeonhole.
4. Conclude the collision.

The Lean version mechanically verifies each step. The paper version
states the cardinality comparison as obvious.

**Transfer check**: You can now recognize pigeonhole in a word problem,
formalize it, prove it in Lean, and restate the proof in ordinary
mathematical language.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
