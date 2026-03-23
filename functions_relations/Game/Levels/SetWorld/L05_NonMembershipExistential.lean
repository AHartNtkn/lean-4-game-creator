import Game.Metadata

World "SetWorld"
Level 5

Title "Disproving Membership in an Existential Set"

Introduction "
# Non-Membership with Existential Predicates

In Level 3, you proved `7 ∉ {n | n < 5}` — the predicate was a simple
arithmetic comparison, and `omega` dispatched it directly after `show`.

But what happens when the predicate involves an **existential**?

The set `{n : ℕ | Even n}` has predicate `Even n`, which means
`∃ r, n = r + r`. To prove `3 ∉ {n | Even n}`, you must show that
NO witness `r` can satisfy `3 = r + r`.

The proof pattern:
1. `intro h` — assume `3 ∈ {n | Even n}`, giving `h : Even 3`
   (i.e., `h : ∃ r, 3 = r + r`)
2. `obtain ⟨r, hr⟩ := h` — destructure the existential: extract the
   witness `r : ℕ` and the equation `hr : 3 = r + r`
3. `omega` — the equation `3 = r + r` has no natural number solution
   (3 is odd), so `omega` derives `False`

The new tactic here is `obtain`. It takes an existential hypothesis
and breaks it apart into its components. The syntax uses angle brackets:
`obtain ⟨name1, name2⟩ := hypothesis` (type ⟨ as `\\<` and ⟩ as `\\>`).

**Your task**: Prove that 3 is not even.
"

/-- 3 does not belong to the set of even natural numbers. -/
Statement : (3 : ℕ) ∉ {n : ℕ | Even n} := by
  Hint "The goal is `3 ∉ setOf fun n => Even n`, which means
  `Even 3 → False`. Use `intro h` to assume `Even 3`."
  intro h
  Hint "`h : Even 3` means `∃ r, 3 = r + r`. Use
  `obtain ⟨r, hr⟩ := h` to extract the witness `r` and equation
  `hr : 3 = r + r`. (Type ⟨ as `\\<` and ⟩ as `\\>`.)"
  Hint (hidden := true) "`obtain ⟨r, hr⟩ := h` destructures the
  existential. After this, you will have `r : ℕ` and `hr : 3 = r + r`."
  obtain ⟨r, hr⟩ := h
  Hint "Now `hr : 3 = r + r` but 3 is odd — no natural number `r`
  satisfies this. `omega` sees this contradiction and closes the goal."
  Hint (hidden := true) "`omega` handles the linear arithmetic:
  `r + r` is always even, so it can never equal 3."
  omega

Conclusion "
You proved `3 ∉ {n | Even n}` by assuming membership, destructuring
the existential witness, and deriving an arithmetic contradiction.

This is a different proof shape from Level 3:

| Level 3 | This level |
|---|---|
| Predicate: `n < 5` (arithmetic) | Predicate: `Even n` (existential) |
| `show` unfolds to arithmetic | `intro` gets the existential |
| `omega` on the arithmetic | `obtain` extracts witness, THEN `omega` |

Notice the recurring pattern across Levels 2, 3, and this level: **unfold
the set notation, assume or provide, then close with arithmetic**. This is
the *membership reduction* pattern — every set membership question reduces
to a question about the underlying predicate, and the proof works directly
with that predicate. This pattern transfers to every set concept in this
course.

The `obtain` tactic is your tool for destructuring existentials. Whenever
you have `h : ∃ x, P x`, use `obtain ⟨x, hx⟩ := h` to get the witness
`x` and the proof `hx : P x`. You will use this pattern throughout the
course — it appears whenever set membership involves existential
conditions.
"

/-- `obtain ⟨x, hx⟩ := h` destructures a hypothesis `h` with structure
(such as `∃ x, P x` or `⟨a, b⟩`) into its components.

## Syntax
```
obtain ⟨x, hx⟩ := h     -- destructure an existential
obtain ⟨a, b⟩ := h       -- destructure a conjunction or pair
obtain ⟨x, hx, hy⟩ := h  -- nested destructuring
```

## Angle bracket input
Type ⟨ as `\<` and ⟩ as `\>` in the editor.

## When to use it
When you have a hypothesis whose type is an existential `∃ x, P x`,
a conjunction `P ∧ Q`, or any structure with a single constructor.
After `obtain`, the components are available as separate hypotheses.

## Example
If `h : ∃ r, n = r + r`, then `obtain ⟨r, hr⟩ := h` gives
`r : ℕ` and `hr : n = r + r`.
-/
TacticDoc obtain

NewTactic obtain

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
