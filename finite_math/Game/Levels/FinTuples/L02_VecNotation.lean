import Game.Metadata

World "FinTuples"
Level 2

Title "Vec Notation with Variables"

Introduction "
# Tuples Work with Variables Too

The `![...]` notation doesn't just work with concrete numbers.
You can use variables:

If `a b c : ℕ`, then `![a, b, c] : Fin 3 → ℕ` is a 3-tuple
whose values are `a`, `b`, and `c`.

Element access still reduces by definition:
- `![a, b, c] 0 = a`
- `![a, b, c] 1 = b`
- `![a, b, c] 2 = c`

These hold by `rfl` because `![a, b, c]` is *defined* to return
`a` at index 0, `b` at index 1, and `c` at index 2 — regardless
of what `a`, `b`, `c` actually are.

**Your task**: Prove that the first element of `![a, b, c]` is `a`.
"

/-- Accessing the first element of a variable tuple. -/
Statement (a b c : ℕ) : (![a, b, c] : Fin 3 → ℕ) 0 = a := by
  Hint "Even with variables, element access is definitional. Use `rfl`."
  rfl

Conclusion "
The pattern: `![a, b, c] i` reduces to the `i`-th element by
definition.

You can build tuples of any length and with any type:
- `![5] : Fin 1 → ℕ` — a 1-tuple
- `![true, false] : Fin 2 → Bool` — a Bool pair
- `![1, 2, 3, 4] : Fin 4 → ℕ` — a 4-tuple

The type annotation (`: Fin n → α`) is sometimes needed to
help Lean figure out the types.

In the next level, you'll learn to *build* tuples using
pattern-matching syntax.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
