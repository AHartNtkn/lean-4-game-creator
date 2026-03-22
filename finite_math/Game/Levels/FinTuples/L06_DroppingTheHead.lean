import Game.Metadata

World "FinTuples"
Level 6

Title "Dropping the Head"

Introduction "
# Fin.tail: Decomposing Tuples

If `Fin.cons` builds tuples by prepending, **`Fin.tail`**
decomposes them by dropping the first element.

Given a tuple `f : Fin (n + 1) → α`, `Fin.tail f` is the
tuple `Fin n → α` that skips the first element:

$$\\texttt{Fin.tail}\\;f\\;(i) = f\\;(i + 1)$$

For example:
$$\\texttt{Fin.tail}\\;\\texttt{![10, 20, 30]} = \\texttt{![20, 30]}$$

The first element `10` is dropped, and the remaining elements
`20, 30` form a shorter tuple.

Here you're given a function `f` that equals `![a, b, c]`.
First rewrite using the hypothesis, then the tail computes
by definition.

**Your task**: Prove that dropping the head of `f` gives `![b, c]`.
"

/-- `Fin.tail` drops the first element of a tuple. -/
Statement (a b c : ℕ) (f : Fin 3 → ℕ) (hf : f = ![a, b, c]) :
    Fin.tail f = ![b, c] := by
  Hint "First, substitute `f` with its known value using `rw [hf]`."
  rw [hf]
  Hint "Now the goal is `Fin.tail ![a, b, c] = ![b, c]`, which
  holds by definition. Use `rfl`."
  rfl

Conclusion "
`Fin.cons` and `Fin.tail` are complementary operations:

- `Fin.cons` prepends: `Fin.cons a ![b, c] = ![a, b, c]`
- `Fin.tail` drops: `Fin.tail ![a, b, c] = ![b, c]`

Together, they give you the head and the tail of any tuple.
The head is `f 0` (just evaluate at index 0), and the tail is
`Fin.tail f`.

This decomposition — *every non-empty tuple is a head followed
by a tail* — is the tuple analog of how every non-empty list
is a head `::` tail. In the next level, you'll see the formal
identity that ties these pieces together.
"

/-- `Fin.tail f` drops the first element of tuple `f`.

## Syntax
```
Fin.tail f    -- drop the head
```

## Type
`Fin.tail : (Fin (n + 1) → α) → (Fin n → α)`

## Definition
`Fin.tail f i = f i.succ`

## Example
`Fin.tail ![10, 20, 30] = ![20, 30]`

## Key identity
`Fin.cons (f 0) (Fin.tail f) = f` — every tuple equals
its head prepended to its tail (`Fin.cons_self_tail`).
-/
DefinitionDoc Fin.tail as "Fin.tail"

NewDefinition Fin.tail

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
