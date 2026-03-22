import Game.Metadata

World "MeetFin"
Level 13

Title "The Empty Type"

Introduction "
# Fin 0 Has No Elements

What is `Fin 0`? It's the type of natural numbers less than 0.
But no natural number is less than 0, so **`Fin 0` is empty**.

This means: if you ever have `i : Fin 0` in your context, you have
a contradiction. From a contradiction, you can prove anything —
including `False`.

The key insight: `i.isLt` gives a proof of `i.val < 0`, but no
natural number satisfies this. So `omega` can derive `False` from
the contradictory hypothesis.

**Your task**: Given `i : Fin 0`, prove `False`.

Strategy: extract the impossible bound with `have h := i.isLt`,
then close with `omega`.
"

/-- An element of `Fin 0` leads to a contradiction. -/
Statement (i : Fin 0) : False := by
  Hint "Extract the bound proof: `have h := i.isLt`. This gives
  you `h : i.val < 0`, which is impossible for a natural number."
  have h := i.isLt
  Hint "Now `{h}` says a natural number is less than 0. `omega` can
  see this is impossible."
  omega

Conclusion "
`Fin 0` is the **empty type** — it has no elements at all.

If you ever have `i : Fin 0` in your hypotheses, you're in a
contradictory context. The `.isLt` field gives `i.val < 0`, and
since no natural number is less than 0, `omega` derives `False`.

This pattern — extract `.isLt`, close with `omega` — is the **Fin
contradiction pattern**. You already used it in Level 3 (where
`x.val = 5` contradicted `x.val < 5`). You'll use it again in the
case analysis levels ahead, where impossible branches have a value
too large for the bound.

This is an important edge case to keep in mind: `Fin n` for `n = 0`
is qualitatively different from `Fin n` for `n ≥ 1`.

*Alternative approach*: `exact Fin.elim0 i` also works — it's a
built-in function that eliminates any `Fin 0` element.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
