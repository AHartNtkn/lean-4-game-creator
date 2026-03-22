import Game.Metadata

World "MeetFin"
Level 14

Title "From Nothing, Everything"

Introduction "
# The Explosion Principle

In Level 13, you proved that `Fin 0` leads to `False`. But why is
that useful? Because from `False`, you can prove **anything**.

This is the *explosion principle* (ex falso quodlibet): a false
hypothesis implies every statement. If your context contains a
contradiction, every goal is provable.

Here the goal is `42 = 0` — obviously false in normal mathematics.
But you have `i : Fin 0`, which is a contradiction (no natural
number is less than 0). From this contradictory hypothesis, even
`42 = 0` follows.

**Strategy**: Extract the contradiction from `i` the same way
you did in Level 13 (`have h := i.isLt` then `omega`), and `omega`
will close the goal — it sees that the hypotheses are contradictory
and doesn't even need to engage with `42 = 0`.
"

/-- From an element of the empty type, anything follows. -/
Statement (i : Fin 0) : 42 = 0 := by
  Hint "Extract the bound: `have h := i.isLt`. This gives a proof of
  `i.val < 0`, which is impossible."
  have h := i.isLt
  Hint "Now `{h}` says a natural number is less than 0. `omega` sees
  this is contradictory and closes any goal."
  omega

Conclusion "
This is the **explosion principle**: from a contradiction, you can
prove anything. Having `i : Fin 0` is a contradiction because no
natural number is less than 0.

The pattern is the same as Level 13 — the **Fin contradiction pattern** (`have h := i.isLt; omega`) —
but now the goal is an arbitrary false statement instead of `False`
itself. The key insight: `omega` doesn't just prove `False` from
contradictory hypotheses; it closes *any* goal when the hypotheses
are contradictory.

You'll encounter this principle throughout mathematics: whenever
you can show a hypothesis is impossible, the entire branch of
reasoning collapses and every statement in that branch is provable.

*Shortcut*: `exact Fin.elim0 i` does the same thing in one step.
It's the canonical way experienced Lean users handle `Fin 0`.
"

/-- `Fin.elim0` eliminates an element of `Fin 0`. Since `Fin 0` is
empty, this can produce a value of any type.

## Syntax
```
exact Fin.elim0 i
```
where `i : Fin 0`.

## When to use it
When you have `i : Fin 0` in context. Since `Fin 0` has no elements,
`i` is a contradiction, and `Fin.elim0 i` can produce any type.
-/
DefinitionDoc Fin.elim0 as "Fin.elim0"

NewDefinition Fin.elim0

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
