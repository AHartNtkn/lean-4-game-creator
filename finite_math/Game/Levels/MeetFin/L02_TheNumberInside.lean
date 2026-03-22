import Game.Metadata

World "MeetFin"
Level 2

Title "The Number Inside"

Introduction "
# Extracting the Natural Number

Every element `i : Fin n` carries two pieces of data:
- `i.val : ℕ` — the underlying natural number
- `i.isLt : i.val < n` — the proof that it's in range

The field `.val` lets you **extract** the natural number from a `Fin`
element. The field `.isLt` gives you the **bound proof** directly.

Lean also has a *coercion* notation: when a natural number is expected,
you can write `(i : ℕ)` or `↑i` (typed `\\uparrow i`), and Lean
automatically inserts `.val`. So `(i : ℕ)`, `↑i`, and `i.val` all
mean the same thing.

Look at the goal: it says `(↑i : ℕ) = 3`. The hypothesis `h` says
`i.val = 3`. Since `↑i` IS `i.val`, the hypothesis `h` matches the
goal exactly.

**Your task**: Use `exact h` to close the goal.
"

/-- The coercion `↑i` is the same as `i.val`. -/
Statement (i : Fin 5) (h : i.val = 3) : (i : ℕ) = 3 := by
  Hint "The goal `(↑i : ℕ) = 3` is the same as `i.val = 3`. The
  hypothesis `{h}` says exactly `i.val = 3`. Try `exact h`."
  Hint (hidden := true) "`exact h` works because `(i : ℕ)` and `i.val`
  are definitionally the same — Lean sees no difference."
  exact h

Conclusion "
You've just seen that `↑i`, `(i : ℕ)`, and `i.val` are all the same
thing — three notations for extracting the natural number from a `Fin`
element.

| Notation | Meaning |
|---|---|
| `i.val` | Dot notation for the value field |
| `↑i` | Coercion arrow (typed `\\uparrow`) |
| `(i : ℕ)` | Type ascription coercion |

All three are **definitionally equal** in Lean — the type checker
treats them as identical without any proof needed.

The other field, `i.isLt`, gives you a proof that `i.val < n`. You'll
use `.isLt` in the next level to prove a bound.
"

/-- `Fin.val` extracts the underlying natural number from a `Fin n`
element. If `i : Fin n`, then `i.val : ℕ` satisfies `i.val < n`.

The coercion `↑i` (typed `\\uparrow i`) is notation for `i.val`
when a natural number is expected.

## Example
If `i : Fin 5` and `i.val = 3`, then:
- `i.val = 3`
- `(↑i : ℕ) = 3`

## Related
`i.isLt` gives a proof that `i.val < n`.
-/
DefinitionDoc Fin.val as "Fin.val"

NewDefinition Fin.val

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
