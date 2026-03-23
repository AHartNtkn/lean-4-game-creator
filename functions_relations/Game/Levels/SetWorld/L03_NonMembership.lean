import Game.Metadata

World "SetWorld"
Level 3

Title "Non-Membership"

Introduction "
# Non-Membership: `∉` means `¬ ∈`

Just as `x ∈ s` means the predicate `s` holds at `x`, non-membership
`x ∉ s` means the predicate does NOT hold. Formally:

$$x \\notin s \\;\\;\\Longleftrightarrow\\;\\; \\neg\\, (x \\in s) \\;\\;\\Longleftrightarrow\\;\\; (x \\in s) \\to \\text{False}$$

So `7 ∉ {n | n < 5}` unfolds to `¬ (7 < 5)`, which is `7 < 5 → False`.

To prove a negation `¬ P`, you assume `P` and derive a contradiction.
The tactic `intro h` turns a goal `¬ P` into a goal `False` with
hypothesis `h : P`.

**Your task**: First use `show ¬ (7 < 5)` to make the goal explicit.
Then use `intro h` to assume `7 < 5`, and `omega` to derive the
contradiction.
"

/-- 7 does not belong to the set of naturals less than 5. -/
Statement : (7 : ℕ) ∉ {n : ℕ | n < 5} := by
  Hint "Use `show ¬ (7 < 5)` to unfold the set membership and
  non-membership. This reveals the arithmetic content."
  Branch
    intro h
    Hint "You used `intro h` to assume membership, getting
    `h : 7 ∈ setOf fun n => n < 5` and goal `False`.

    While `omega` cannot see through the set-membership wrapper directly,
    the `contradiction` tactic can — it detects that `h` is definitionally
    `7 < 5`, which is impossible. Try `contradiction`.

    (The main path uses `show ¬ (7 < 5)` first to make the arithmetic
    explicit before introducing — both approaches are valid.)"
    Hint (hidden := true) "`contradiction` examines your hypotheses for
    contradictions, even through definitional wrappers like set membership."
    contradiction
  show ¬ (7 < 5)
  Hint "The goal is `¬ (7 < 5)`, which means `7 < 5 → False`. Use
  `intro h` to assume `7 < 5`."
  intro h
  Hint "Now `h` says `7 < 5`, which is impossible. `omega` sees the
  contradiction and closes the goal."
  Hint (hidden := true) "`omega` examines all arithmetic hypotheses.
  Since `h : 7 < 5` contradicts basic arithmetic, it derives `False`."
  omega

Conclusion "
The proof pattern for non-membership:

1. `show ¬ (P x)` — unfold `x ∉ {y | P y}` to its arithmetic content
2. `intro h` — assume `P x`, changing the goal to `False`
3. Derive the contradiction (here, `omega` saw that `h : 7 < 5` is
   impossible)

The `show ... ; intro h; omega` pattern works whenever the predicate
is a false arithmetic statement. For non-arithmetic predicates, you
will use other tools to derive `False` from the hypothesis.

In ordinary mathematics, this is a *proof by contradiction*: assume
7 is in the set, observe this means 7 < 5, which is absurd.
"

NewTactic contradiction

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
