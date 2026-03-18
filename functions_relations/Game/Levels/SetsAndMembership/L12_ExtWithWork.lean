import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 12

Title "Extensionality with Real Work"

Introduction
"
In the last level, each direction of the iff was a single hypothesis
application. Now you will use `ext` on sets where the chase step
requires real logical work.

You need to prove that the set of `x` satisfying `P x ∧ Q x` equals
the set of `x` satisfying `Q x ∧ P x`. After `ext x` and `constructor`,
each direction requires you to take apart a conjunction and rebuild it
with the components swapped.

Remember: `obtain ⟨hp, hq⟩ := h` splits a conjunction hypothesis
`h : P ∧ Q` into `hp : P` and `hq : Q`. And `exact ⟨hq, hp⟩`
builds a conjunction from its components.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem and_comm And.comm

Statement (P Q : ℕ → Prop) :
    ({x : ℕ | P x ∧ Q x} : Set ℕ) = {x : ℕ | Q x ∧ P x} := by
  Hint "Start with `ext x` to reduce to elementwise equivalence."
  ext x
  Hint "Good. The goal is `P x ∧ Q x ↔ Q x ∧ P x` (after unfolding
  set-builder notation). Use `constructor` to split into the two directions."
  constructor
  · Hint "Forward direction: assume `P x ∧ Q x`, prove `Q x ∧ P x`.
    Use `intro h` then `obtain ⟨hp, hq⟩ := h` to split the conjunction."
    intro h
    obtain ⟨hp, hq⟩ := h
    Hint "Now build the swapped conjunction. Try `exact ⟨hq, hp⟩`."
    exact ⟨hq, hp⟩
  · Hint "Backward direction: same idea, reversed.
    Use `intro h` then `obtain ⟨hq, hp⟩ := h`."
    intro h
    obtain ⟨hq, hp⟩ := h
    exact ⟨hp, hq⟩

Conclusion
"
You proved a nontrivial set equality by reducing it to logic with `ext`
and then doing real work in each direction.

The proof had three phases:
1. **Reduce**: `ext x` turns set equality into an iff about membership.
2. **Split**: `constructor` gives you forward and backward directions.
3. **Chase**: In each direction, you took apart a conjunction and rebuilt
   it with components swapped.

Notice that *no set-specific reasoning* was needed after `ext` — the
proof became pure logic. This is the power of extensionality: it reduces
set-theoretic questions to logical ones.
"
