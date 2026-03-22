import Game.Metadata

World "MeetFin"
Level 9

Title "The Round-Trip Property"

Introduction "
# Taking Apart and Reassembling

In Level 1, you *constructed* a `Fin` element with `⟨k, by omega⟩`.
In Level 2, you *extracted* its parts with `.val` and `.isLt`.

A natural question: if you know an element's value, can you identify
it with an explicit `⟨k, proof⟩` term?

Here you have `i : Fin 5` and a hypothesis `h : i.val = 3`. The
goal asks you to show `i = ⟨3, by omega⟩` — that `i` is the
element with value 3.

**Strategy**: Use `rw [Fin.ext_iff]` to reduce the `Fin` equality
to a value equality, then use `h` to close.
"

/-- If a Fin element has value 3, it equals the explicit construction ⟨3, _⟩. -/
Statement (i : Fin 5) (h : i.val = 3) : i = ⟨3, by omega⟩ := by
  Hint "Use `rw [Fin.ext_iff]` to convert the `Fin` equality to a
  value equality."
  rw [Fin.ext_iff]
  Hint "The goal is now `i.val = 3`, which is exactly `{h}`."
  exact h

Conclusion "
The round-trip principle: if you know what value a `Fin` element
carries, you can identify it with the explicit construction.

This pattern has a name in Lean's library: **`Fin.eta`**. It says
that any `Fin` element `i` equals `⟨i.val, i.isLt⟩` — its own
reconstruction from components.

Here you proved a specific case: given `h : i.val = 3`, you showed
`i = ⟨3, by omega⟩`. In the next level, you'll prove the **general**
version — that `i = ⟨i.val, i.isLt⟩` for any `i`, with no hypothesis
needed.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
