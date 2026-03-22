import Game.Metadata

World "FinTuples"
Level 1

Title "Functions as Tuples"

Introduction "
# Functions from Fin as Tuples

In the previous worlds, you learned that `Fin n` is the type of
natural numbers less than `n`. Now comes a key insight:

**A function `Fin n → α` is the same thing as an `n`-tuple** — an
ordered list of `n` elements from `α`.

Why? A function from `Fin 3 → ℕ` is determined by three values:
what it returns at `0`, at `1`, and at `2`. Those three values, in
order, form a triple. Conversely, any triple $(a_0, a_1, a_2)$
defines a function `Fin 3 → ℕ` by $i \\mapsto a_i$.

In Lean, `![10, 20, 30]` creates a function `Fin 3 → ℕ` that
returns `10` at index `0`, `20` at index `1`, and `30` at index `2`.
The `!` prefix distinguishes this from a plain list — it's a
**vector** (a function from `Fin n`), not a linked list.

**Your task**: Verify that the element at index 1 of `![10, 20, 30]`
is `20`. (Remember: indexing starts at 0.)
"

/-- The element at index 1 of `![10, 20, 30]` is 20. -/
Statement : (![10, 20, 30] : Fin 3 → ℕ) 1 = 20 := by
  Hint "The value `![10, 20, 30] 1` reduces to `20` by definition.
  Use `rfl`."
  rfl

Conclusion "
You just accessed an element of a 3-tuple. The key idea:

$$\\texttt{![10, 20, 30]}$$

creates a function `Fin 3 → ℕ`. Evaluating it at index `1` gives
`20` — the second element (counting from 0).

This is analogous to subscript notation in mathematics:
if $v = (10, 20, 30)$, then $v_1 = 20$.
In Lean, `v 1` plays the role of $v_1$.

Since the value is determined by the definition, `rfl` closes
the equation.

Notice the type: `Fin 3 → ℕ`. The domain `Fin 3` has exactly 3
elements, so the function is completely determined by 3 values —
it's a 3-tuple. More generally, `Fin n → α` is an `n`-tuple. The
number of elements in the tuple IS the number of elements in `Fin n`.
This connection between tuple length and `Fin n` cardinality will be
formalized in the Cardinality world.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
