import Game.Metadata

World "CountingTechniques"
Level 15

Title "Pushing Negations with push_neg"

Introduction "
# New Tactic: `push_neg`

In the next level, you'll prove pigeonhole from fiber decomposition
using a proof by contradiction. The key step: after assuming the
negation of 'some fiber is large', you need to transform

`not (exists b, 1 < fiber_size b)`

into the more useful

`forall b, fiber_size b <= 1`

The tactic `push_neg` does exactly this. It pushes negations inward
through quantifiers and connectives:

| Before `push_neg` | After `push_neg` |
|---|---|
| `not (forall x, P x)` | `exists x, not P x` |
| `not (exists x, P x)` | `forall x, not P x` |
| `not (a < b)` | `b <= a` |
| `not (a <= b)` | `b < a` |

**Syntax**: `push_neg at h` transforms hypothesis `h`.
`push_neg` (no `at`) transforms the goal.

**Your task**: Given `h : not (forall i, sizes i <= 1)`, transform
it with `push_neg` and close the goal.
"

/-- If not every bin has at most 1 item, then some bin has more than 1 item. -/
Statement (n : ℕ) (sizes : Fin n → ℕ)
    (h : ¬∀ i, sizes i ≤ 1) : ∃ i, 1 < sizes i := by
  Hint "Use `push_neg at h` to transform the negated universal
  quantifier into an existential."
  Hint (hidden := true) "Try `push_neg at h`."
  push_neg at h
  Hint "After `push_neg`, `h` is now `exists i, 1 < sizes i` —
  exactly the goal."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`push_neg` in action:
1. `push_neg at h` — transform `not (forall i, sizes i <= 1)` into
   `exists i, 1 < sizes i`
2. `exact h` — the transformed hypothesis matches the goal

**How `push_neg` works**: It applies De Morgan's laws and
order duals systematically:
- `not forall` becomes `exists ... not`
- `not exists` becomes `forall ... not`
- `not (a <= b)` becomes `b < a`
- `not (a < b)` becomes `b <= a`

**When to reach for `push_neg`**: After `by_contra` gives you a
negated hypothesis. The raw negation (`not exists ...` or
`not forall ...`) is hard to work with. `push_neg` converts it
to a positive statement you can use directly.

**Coming up**: The averaging argument (next level) uses exactly
this pattern: `by_contra` to assume no fiber is large, then
`push_neg` to get 'every fiber is small', then derive a
contradiction from the fiber sum.
"

NewTactic push_neg

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
