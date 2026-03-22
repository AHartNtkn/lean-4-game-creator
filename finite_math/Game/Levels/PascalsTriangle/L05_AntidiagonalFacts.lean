import Game.Metadata

World "PascalsTriangle"
Level 5

Title "Antidiagonal Facts"

Introduction "
# Size and Base Case

Two basic facts about antidiagonals:

**Size**: The antidiagonal of $n$ contains the pairs
$(0, n), (1, n-1), \\ldots, (n, 0)$ — that is, $n + 1$ pairs:

```
Finset.Nat.card_antidiagonal :
  (Finset.antidiagonal n).card = n + 1
```

This connects to Pascal's triangle: row $n$ has $n + 1$ entries
(from $\\binom{n}{0}$ to $\\binom{n}{n}$), and the antidiagonal
has $n + 1$ pairs — one pair per entry.

**Base case**: The antidiagonal of $0$ has exactly one pair:

```
Finset.Nat.antidiagonal_zero :
  Finset.antidiagonal 0 = {(0, 0)}
```

This is the base case for any induction on the antidiagonal.

**Your task**: Prove both facts.
"

/-- `Finset.Nat.card_antidiagonal` states that
`(Finset.antidiagonal n).card = n + 1`.

## Syntax
```
exact Finset.Nat.card_antidiagonal n
rw [Finset.Nat.card_antidiagonal]
```

## When to use it
When you need to know the size of an antidiagonal.

## Example
`Finset.Nat.card_antidiagonal 4 : (antidiagonal 4).card = 5`
-/
TheoremDoc Finset.Nat.card_antidiagonal as "Finset.Nat.card_antidiagonal" in "Finset"

/-- `Finset.Nat.antidiagonal_zero` states that
`Finset.antidiagonal 0 = {(0, 0)}`.

## Syntax
```
exact Finset.Nat.antidiagonal_zero
rw [Finset.Nat.antidiagonal_zero]
```

## When to use it
When simplifying a sum or expression involving `antidiagonal 0` —
the base case in inductions over antidiagonal.
-/
TheoremDoc Finset.Nat.antidiagonal_zero as "Finset.Nat.antidiagonal_zero" in "Finset"

/-- Two basic antidiagonal facts: the size and the base case. -/
Statement : (Finset.antidiagonal 4).card = 5 ∧ Finset.antidiagonal 0 = {(0, 0)} := by
  Hint "Use `constructor` to split the conjunction into two goals."
  Hint (hidden := true) "Try `constructor`."
  constructor
  Hint "First goal: the 4th antidiagonal has 5 elements.
  Apply `Finset.Nat.card_antidiagonal` directly."
  Hint (hidden := true) "Try `exact Finset.Nat.card_antidiagonal 4`."
  exact Finset.Nat.card_antidiagonal 4
  Hint "Second goal: the 0th antidiagonal is the singleton.
  Apply `Finset.Nat.antidiagonal_zero` directly."
  Hint (hidden := true) "Try `exact Finset.Nat.antidiagonal_zero`."
  exact Finset.Nat.antidiagonal_zero

Conclusion "
`antidiagonal 4` has 5 elements:
$(0,4), (1,3), (2,2), (3,1), (4,0)$.

And `antidiagonal 0 = \\{(0, 0)\\}$ — the only pair of natural numbers
summing to 0 is $(0, 0)$.

**The antidiagonal encodes Pascal's identity**. Each pair $(i, j)$
with $i + j = n + 1$ comes from either $(i - 1, j)$ or
$(i, j - 1)$ in `antidiagonal n`. The antidiagonal is the
**geometric encoding** of Pascal's triangle, where each entry
is the sum of the two entries on the previous antidiagonal.
"

NewTheorem Finset.Nat.card_antidiagonal Finset.Nat.antidiagonal_zero

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
