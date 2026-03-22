import Game.Metadata

World "MeetFin"
Level 22

Title "Existential Witnesses"

Introduction "
# Providing a Fin Element as a Witness

In Level 1, you constructed a `Fin` element with `exact ⟨k, by omega⟩`.
But what if the goal asks you to prove that *some* element exists
with a property? Then you need `use` to provide the witness.

When the goal is `∃ x : Fin n, P x`, the tactic `use ⟨k, by omega⟩`
provides a specific `Fin n` element as the witness, then asks you
to prove `P` holds for that element.

This combines two skills you already know:
- `use` from the NNG4 prerequisites (providing existential witnesses)
- `⟨k, by omega⟩` from Level 1 (constructing `Fin` elements)

**Your task**: Find a `Fin 5` element whose value is `3`.
"

/-- There exists an element of `Fin 5` with value `3`. -/
Statement : ∃ x : Fin 5, x.val = 3 := by
  Hint "Provide the witness with `use ⟨3, by omega⟩`. This constructs
  the element `3 : Fin 5` and provides it as the existential witness.
  The remaining goal `3 = 3` closes automatically."
  Hint (hidden := true) "`use ⟨3, by omega⟩` provides the witness and
  Lean closes `3 = 3` by reflexivity."
  use ⟨3, by omega⟩

Conclusion "
The pattern `use ⟨k, by omega⟩` provides a `Fin` element as an
existential witness. This is simply the combination of two moves:

| Move | From |
|---|---|
| `use expr` — provide a witness | NNG4 prerequisites |
| `⟨k, by omega⟩` — construct a Fin element | Level 1 |

You'll use this combination in the boss.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
