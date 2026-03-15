import GameServer.Commands
import Mathlib

World "CountingFunctions"
Level 2

Title "Counting injective functions"

Introduction
"
# Which Functions Are Injective?

Of the 9 functions from `Fin 2` to `Fin 3`, how many are **injective**
(one-to-one)?

An injective function `f : Fin 2 → Fin 3` maps distinct inputs to
distinct outputs. Since there are only 2 inputs (0 and 1), injectivity
means $f(0) \\neq f(1)$.

Counting: for $f(0)$, there are 3 choices. For $f(1)$, we must avoid
the value already used by $f(0)$, leaving 2 choices. That gives
$3 \\times 2 = 6$ injective functions.

## Embeddings in Lean

In Lean, injective functions from `α` to `β` are represented as
**embeddings**: `α ↪ β`. The cardinality of embeddings is given by:
```
Fintype.card_embedding_eq :
  Fintype.card (α ↪ β) = (Fintype.card β).descFactorial (Fintype.card α)
```

The **descending factorial** `n.descFactorial k` is the product
$n \\cdot (n-1) \\cdots (n-k+1)$. For $n = 3$, $k = 2$:
$3 \\cdot 2 = 6$.

## Your task

Prove that `Fintype.card (Fin 2 ↪ Fin 3) = 6`.
"

/-- There are exactly 6 injective functions (embeddings) from
`Fin 2` to `Fin 3`. -/
Statement : Fintype.card (Fin 2 ↪ Fin 3) = 6 := by
  Hint "Use `rw [Fintype.card_embedding_eq]` to rewrite the embedding
  cardinality as a descending factorial."
  rw [Fintype.card_embedding_eq]
  Hint "The goal is now
  `(Fintype.card (Fin 3)).descFactorial (Fintype.card (Fin 2)) = 6`.
  Rewrite the `Fintype.card (Fin _)` terms."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `Nat.descFactorial 3 2 = 6`. Use `norm_num`
  (or `rfl`) to close it."
  norm_num

Conclusion
"
There are exactly 6 injective functions from `Fin 2` to `Fin 3`.

The proof used:
1. `Fintype.card_embedding_eq` to express the count as a descending
   factorial: $3.\\text{descFactorial}\\ 2$.
2. `Fintype.card_fin` to evaluate: $3.\\text{descFactorial}\\ 2 =
   3 \\cdot 2 = 6$.

## The 6 injective functions

Listed as $(f(0), f(1))$:

$(0,1), (0,2), (1,0), (1,2), (2,0), (2,1)$

These are exactly the 6 functions where $f(0) \\neq f(1)$. The
3 excluded functions --- $(0,0)$, $(1,1)$, $(2,2)$ --- all have
$f(0) = f(1)$, violating injectivity.

## Injections vs. all functions

| Type | Count | Formula |
|------|-------|---------|
| All functions | 9 | $3^2$ |
| Injections | 6 | $3 \\cdot 2$ |
| Non-injections | 3 | $9 - 6$ |

The ratio: $6/9 = 2/3$ of the functions are injective. As the domain
grows, this ratio drops quickly --- most functions from large sets to
same-size sets are not injective.

**In plain language**: \"From a 2-element set to a 3-element set, there
are $3 \\cdot 2 = 6$ injective functions: 3 choices for the first image,
then 2 remaining choices for the second.\"
"

/-- `Fintype.card_embedding_eq` states that the number of embeddings
(injective functions) from `α` to `β` is the descending factorial:
```
Fintype.card_embedding_eq :
  Fintype.card (α ↪ β) = (Fintype.card β).descFactorial (Fintype.card α)
```

The descending factorial `n.descFactorial k` is `n * (n-1) * ... * (n-k+1)`.

**When to use**: When counting injective functions between finite types. -/
TheoremDoc Fintype.card_embedding_eq as "Fintype.card_embedding_eq" in "Fintype"

/-- `Nat.descFactorial n k` is the descending factorial: the product
`n * (n-1) * ... * (n-k+1)`. It equals `n! / (n-k)!` when `k ≤ n`,
and `0` when `k > n`.

**Examples**:
- `Nat.descFactorial 3 2 = 3 * 2 = 6`
- `Nat.descFactorial 5 3 = 5 * 4 * 3 = 60`

**When to use**: When counting injective functions (embeddings) or
ordered selections without replacement. -/
DefinitionDoc Nat.descFactorial as "Nat.descFactorial"

NewTheorem Fintype.card_embedding_eq
NewDefinition Nat.descFactorial
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
