import Game.Metadata

World "PsetFin"
Level 6

Title "Vacuous Truth"

Introduction "
# When There Are No Cases

In MeetFin, you proved that `Fin 0` has no elements and that
`Fin.elim0` eliminates any `Fin 0` value. Here's the punchline:
any universally quantified statement about `Fin 0` is **vacuously
true** — there are no elements to check.

**Your task**: Prove that every element of `Fin 0` satisfies an
arbitrary predicate `P`. Since there are no elements, there's
nothing to verify.
"

/-- Any predicate holds vacuously for all elements of Fin 0. -/
Statement (P : Fin 0 → Prop) : ∀ i : Fin 0, P i := by
  Hint "Introduce the element `i : Fin 0`, then eliminate it."
  intro i
  Hint "Since `Fin 0` has no elements, `i` cannot exist.
  Use `exact Fin.elim0 i` to close any goal."
  exact Fin.elim0 i

Conclusion "
`Fin.elim0 i` works for ANY goal type — not just `False` or
`42 = 0` as you saw in MeetFin. If `i : Fin 0`, then `Fin.elim0 i`
produces a value of any type, because the empty type has no
inhabitants to contradict.

This is the logical principle of **vacuous truth**: 'for all x
in the empty set, P(x)' is true because there are no
counterexamples to find.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Subsingleton.elim Unique.eq_default
