import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 9

Title "If and Only If"

Introduction
"
Before we can prove two sets are equal, we need to work with **if and
only if** (`↔`). The statement `P ↔ Q` means 'P implies Q and Q
implies P.'

To **prove** `P ↔ Q`, use `constructor` to split it into two goals:
- the forward direction `P → Q`
- the backward direction `Q → P`

Then prove each direction separately.

In this level, you have two hypotheses — one for each direction — and
need to combine them into an iff. This is the simplest iff proof:
split with `constructor`, then supply each direction.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : P ↔ Q := by
  Hint "The goal is `P ↔ Q`. Use `constructor` to split it into the
  forward direction `P → Q` and the backward direction `Q → P`."
  constructor
  Hint "The goal is `P → Q`. You already have `hpq : P → Q` as a hypothesis.
  Use `exact hpq`."
  · exact hpq
  Hint "The goal is `Q → P`. You already have `hqp : Q → P`.
  Use `exact hqp`."
  · exact hqp

Conclusion
"
You proved an iff statement by splitting it into two directions with
`constructor` and supplying each one.

**Iff proof recipe**:
1. `constructor` — splits `P ↔ Q` into two subgoals
2. Prove `P → Q` (the forward direction)
3. Prove `Q → P` (the backward direction)

In the next level, you will learn how to *use* an iff hypothesis.
"
