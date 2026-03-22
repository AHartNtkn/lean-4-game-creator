import Game.Metadata

World "PsetFin"
Level 8

Title "Obtain: Existential Destructuring"

Introduction "
# The obtain Tactic

In MeetFin Level 16, you saw that `obtain` destructures a value
into its components — an alternative to `cases` for types with
one constructor.

`obtain` is most useful with **existential hypotheses**. If you
have `h : exists j, P j`, then:

> `obtain (j, hj) := h`

gives you `j` (the witness) and `hj : P j` (the property) as
separate hypotheses. This is the standard way to destructure
existentials in real Lean code.

(In actual Lean syntax, use angle brackets: `obtain ⟨j, hj⟩ := h`.)

**Your task**: Given that `i` is a `castSucc` image, prove its
value is less than 3.
"

/-- A castSucc image has value less than n. -/
Statement (i : Fin 4) (h : ∃ j : Fin 3, i = j.castSucc) :
    i.val < 3 := by
  Hint "Destructure the existential: `obtain ⟨j, hj⟩ := h`.
  This gives you the witness `j` and the equation `hj`."
  obtain ⟨j, hj⟩ := h
  Hint "Rewrite `i` using the equation: `rw [hj]`."
  rw [hj]
  Hint "Now the goal is `j.castSucc.val < 3`.
  Simplify with `rw [Fin.val_castSucc]`."
  Hint (hidden := true) "After the rewrite, the goal is `j.val < 3`,
  which is `j.isLt`. Use `exact j.isLt`."
  rw [Fin.val_castSucc]
  exact j.isLt

Conclusion "
`obtain ⟨witness, property⟩ := h` is the standard idiom for
working with existential hypotheses in Lean.

Compare with what you already know:
- `cases h with | intro j hj =>` — also works, but more verbose
- `obtain ⟨j, hj⟩ := h` — cleaner, preferred in practice

The pattern:
1. `obtain ⟨j, hj⟩ := h` — destructure the existential
2. `rw [hj]` — substitute the equation
3. Val lemma + `exact` — close with the bound
"

/-- `obtain` destructures a hypothesis into its components.

## Syntax
```
obtain ⟨x, hx⟩ := h      -- existential: ∃ x, P x
obtain ⟨a, b⟩ := h         -- conjunction: P ∧ Q
obtain ⟨v, hlt⟩ := x       -- structure: Fin n
```

## When to use it
When you have a hypothesis `h` whose type is a structure, existential,
or conjunction, and you want to name the components. This is the
standard Lean idiom — preferred over `cases` for single-constructor
destructuring.
-/
TacticDoc obtain

NewTactic obtain

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
