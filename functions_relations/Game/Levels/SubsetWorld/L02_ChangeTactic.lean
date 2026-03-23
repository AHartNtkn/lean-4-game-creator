import Game.Metadata

World "SubsetWorld"
Level 2

Title "The Change Tactic"

Introduction "
# Unwrapping Hypotheses with `change`

In Level 1, you used `show` to unwrap the **goal** from set notation
to arithmetic, and `have` to extract the hypothesis content. Both
techniques work, but there is a more direct tool for hypotheses.

The tactic `change P at hx` converts `hx` to display as `P`, just
as `show P` does for the goal. Both require `P` to be
**definitionally equal** to the current type. They only change the
*display*, not the *meaning*.

After `intro x hx`, the hypothesis `hx : x ∈ {n | n < 3}` is
definitionally `x < 3`. Use `change x < 3 at hx` to make this
explicit. Then `show x ≤ 3` unwraps the goal, and `exact le_of_lt hx`
closes it — since being strictly less than 3 implies being at most 3.

**Proof plan**:
1. `intro x hx` — fix an element and assume `x ∈ {n | n < 3}`
2. `change x < 3 at hx` — unwrap the hypothesis to arithmetic
3. `show x ≤ 3` — unwrap the goal to arithmetic
4. `exact le_of_lt hx` — derive `x ≤ 3` from `x < 3`
"

/-- Every natural number less than 3 is at most 3. -/
Statement : {n : ℕ | n < 3} ⊆ {n | n ≤ 3} := by
  Hint "Start with `intro x hx` as always for a `⊆` proof."
  intro x hx
  Hint "Now `hx` says `x` is in the left set — the arithmetic fact `x < 3`
  is hidden inside the set notation. Use `change x < 3 at hx` to unwrap it.

  (`change` is like `show` but works on hypotheses: `change P at h`
  converts `h` to display as `P`.)"
  Hint (hidden := true) "`change x < 3 at hx` replaces the set-membership
  form of `hx` with `hx : x < 3`. Then `show x ≤ 3` unwraps the goal
  and `exact le_of_lt hx` closes it."
  change x < 3 at hx
  Hint "Good — `hx` is now `x < 3`. The goal is definitionally `x ≤ 3`.
  Use `show x ≤ 3` to make it explicit."
  show x ≤ 3
  Hint "The hypothesis says `x < 3` and the goal is `x ≤ 3`. The library
  fact `le_of_lt` says that strict inequality implies weak inequality:
  `le_of_lt : a < b → a ≤ b`. Use `exact le_of_lt hx`."
  Hint (hidden := true) "`exact le_of_lt hx` — `le_of_lt` converts
  `hx : x < 3` into a proof of `x ≤ 3`."
  Branch
    exact Nat.le_of_lt hx
  exact le_of_lt hx

Conclusion "
You now have both halves of the unwrapping toolkit:

| Tactic | Target | Effect |
|---|---|---|
| `show P` | Goal | Converts goal to `P` (def-equal) |
| `change P at h` | Hypothesis | Converts `h` to `P` (def-equal) |
| `change P` | Goal | Same as `show P` |

**`change` vs `show`**: They are the same concept applied to different
targets. `show P` changes the goal to `P`. `change P at h` changes
hypothesis `h` to `P`. Both require `P` to be definitionally equal
to the current type — they only change the *display*, not the *meaning*.

Note that `change` is a **convenience** tool for readability — Lean
can often see through the definitional wrapper without it. But when
the proof state has `hx : x ∈ {n | n < 3}` instead of `hx : x < 3`,
`change` makes the arithmetic content visible so you can find the
right closing move. You will use `change` throughout this course.
"

/-- `change P at h` converts hypothesis `h` to display as `P`,
where `P` must be definitionally equal to the current type of `h`.

`change P` (without `at`) converts the goal to `P` — this is
equivalent to `show P`.

## Syntax
```
change P at h    -- convert hypothesis h to P
change P         -- convert the goal to P (same as show P)
```

## When to use it
When a hypothesis is wrapped in notation (like set membership) and
you need the underlying content (like an arithmetic inequality).

## Example
```
-- hx : x ∈ {n | n < 3}
change x < 3 at hx
-- hx : x < 3
```

## Warning
`change` only changes the display — the new type must be
**definitionally equal** to the old one. If Lean rejects the
`change`, the types are not definitionally equal.
-/
TacticDoc «change»

/-- `le_of_lt` proves `a ≤ b` from `a < b` — strict inequality
implies weak inequality.

## Statement
```
le_of_lt : a < b → a ≤ b
```

## When to use it
When you have `h : a < b` and need `a ≤ b`.
-/
TheoremDoc le_of_lt as "le_of_lt" in "Order"

NewTactic «change»
NewTheorem le_of_lt

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith omega
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
