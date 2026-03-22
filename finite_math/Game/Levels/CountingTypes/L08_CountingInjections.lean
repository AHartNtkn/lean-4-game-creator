import Game.Metadata

World "CountingTypes"
Level 8

Title "Counting Injections"

Introduction "
# Injections and the Falling Factorial

An **injection** (or **embedding**) `Fin k ↪ Fin n` is a function
where distinct inputs always give distinct outputs — no two elements
of `Fin k` map to the same element of `Fin n`.

How many injections are there from `Fin k` to `Fin n`? For the first
element you have `n` choices; for the second, only `n - 1` remain (you
can't repeat). This is exactly the falling factorial $n^{\\underline{k}}$.

The general theorem is `Fintype.card_embedding_eq`:

```
Fintype.card (α ↪ β) = (Fintype.card β).descFactorial (Fintype.card α)
```

**Your task**: Given `k = 2` and `n = 5`, prove there are 20
injections from `Fin k` to `Fin n`. First apply `card_embedding_eq`,
then evaluate the `Fin` cardinalities, substitute the concrete values,
and unfold the falling factorial.
"

/-- There are 20 injections from Fin 2 to Fin 5. -/
Statement (k n : ℕ) (hk : k = 2) (hn : n = 5) :
    Fintype.card (Fin k ↪ Fin n) = 20 := by
  Hint "Start with `rw [Fintype.card_embedding_eq]` to convert the
  embedding count to a falling factorial:
  `(Fintype.card (Fin n)).descFactorial (Fintype.card (Fin k))`."
  rw [Fintype.card_embedding_eq]
  Hint "Now evaluate the `Fin` cardinalities:
  `rw [Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint "Substitute the concrete values: `rw [hn, hk]`."
  Hint (hidden := true) "Try `rw [hn, hk]`."
  rw [hn, hk]
  Hint "The goal is `5.descFactorial 2 = 20`. Unfold the falling
  factorial: two `descFactorial_succ` rewrites, then `descFactorial_zero`."
  Hint (hidden := true) "Try
  `rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]

Conclusion "
$$|\\text{Fin}\\;2 \\hookrightarrow \\text{Fin}\\;5| = 5^{\\underline{2}} = 5 \\times 4 = 20$$

This connects two ideas:
- **Falling factorial** `n.descFactorial k` counts ordered selections
  without replacement
- **Embeddings** `α ↪ β` are injective functions — exactly the
  formalization of 'selection without replacement'

| Functions | Count | Formula |
|---|---|---|
| All functions `Fin k → Fin n` | $n^k$ | `card_fun` |
| Injections `Fin k ↪ Fin n` | $n^{\\underline{k}}$ | `card_embedding_eq` |
| Permutations `Fin n ≃ Fin n` | $n!$ | `descFactorial_self` |

**Falling factorial vs. power**: Since injections are a subset of all
functions, we always have $n^{\\underline{k}} \\leq n^k$. The gap
$n^k - n^{\\underline{k}}$ counts the non-injective functions — those
that 'waste' a slot by mapping two inputs to the same output. The boss
will compute this gap for a specific case.

**Looking ahead — combinations**: The falling factorial counts
*ordered* selections. If you don't care about order, divide by $k!$
(the number of orderings of the `k` selected items):

$$\\binom{n}{k} = \\frac{n^{\\underline{k}}}{k!}$$

This is the **binomial coefficient** $C(n,k)$, counting unordered
subsets of size `k`. You'll meet this formally in the Binomial
Coefficients world.
"

/-- `Fintype.card_embedding_eq` counts the number of injections
(embeddings) between two finite types:

`Fintype.card (α ↪ β) = (Fintype.card β).descFactorial (Fintype.card α)`

## Syntax
```
rw [Fintype.card_embedding_eq]
```

## When to use it
When the goal involves `Fintype.card (α ↪ β)` and you want to
convert it to a falling factorial computation.
-/
TheoremDoc Fintype.card_embedding_eq as "Fintype.card_embedding_eq" in "Fintype"

NewTheorem Fintype.card_embedding_eq

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl

-- Force full recursive unfolding
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self
