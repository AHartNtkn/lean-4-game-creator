import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 7

Title "Comparing Nat and Finset induction"

Introduction
"
# When to use which induction principle

Not every theorem about finsets calls for finset induction. Sometimes
**Nat induction** is the right tool — especially when the statement
is parametrized by a natural number rather than an arbitrary finset.

## Example: `(Finset.range n).card = n`

The statement `(Finset.range n).card = n` is about `Finset.range`,
but it is parametrized by `n : Nat`. The natural proof strategy is
Nat induction on `n`:

- **Base case** (`n = 0`): `(Finset.range 0).card = 0`.
  Use `Finset.range_zero` to show `range 0 = ∅`, then `card_empty`.

- **Inductive step** (`n → n + 1`):
  `(Finset.range (n + 1)).card = n + 1`.
  Use `Finset.range_add_one` to rewrite `range (n + 1)` as
  `insert n (range n)`. Then show `n ∉ range n` (since
  `mem_range` gives `n < n`, which is false). Apply
  `card_insert_of_notMem` and the inductive hypothesis.

## Key lemmas

- `Finset.range_zero : Finset.range 0 = ∅`
- `Finset.range_add_one : Finset.range (n + 1) = insert n (Finset.range n)`
- `Finset.mem_range : m ∈ Finset.range n ↔ m < n`

## Your task

Prove `(Finset.range n).card = n` by Nat induction.
"

/-- The cardinality of `range n` is `n`, proved by Nat induction. -/
Statement (n : Nat) : (Finset.range n).card = n := by
  Hint "Use `induction n with` (ordinary Nat induction, not Finset induction)."
  induction n with
  | zero =>
    Hint "The base case: `(Finset.range 0).card = 0`.
    Use `rw [Finset.range_zero, Finset.card_empty]`."
    rw [Finset.range_zero, Finset.card_empty]
  | succ n ih =>
    Hint "The inductive step: prove `(Finset.range (n + 1)).card = n + 1`.
    First, rewrite `range (n + 1)` as `insert n (range n)` using
    `rw [Finset.range_add_one]`."
    rw [Finset.range_add_one]
    Hint "Now you need to show `(insert n (Finset.range n)).card = n + 1`.
    To use `card_insert_of_notMem`, you must prove `n ∉ Finset.range n`.
    Use `have hmem : n ∉ Finset.range n` and prove it with
    `rw [Finset.mem_range]` then `omega`."
    Hint (hidden := true) "Use:
    ```
    have hmem : n ∉ Finset.range n := by
      rw [Finset.mem_range]
      omega
    rw [Finset.card_insert_of_notMem hmem, ih]
    ```"
    have hmem : n ∉ Finset.range n := by
      rw [Finset.mem_range]
      omega
    rw [Finset.card_insert_of_notMem hmem, ih]

Conclusion
"
You proved `card (range n) = n` by Nat induction.

## Choosing the right induction principle

This proof used **Nat induction** because:
- The statement is parametrized by `n : Nat`.
- The recursive structure of `range` follows `Nat`:
  `range 0 = ∅` and `range (n+1) = insert n (range n)`.
- Nat induction matches this recursive structure perfectly.

If you tried **Finset induction** here, you would be proving the property
for all finsets — but `range n` is a *specific* finset determined by `n`.
The universal quantifier is over `n`, not over an arbitrary finset.

## Rule of thumb

| Parametrized by | Use |
|---|---|
| `n : Nat` | `induction n with` |
| `s : Finset α` | `induction s using Finset.induction_on` |

**In plain language**: \"The set {0, 1, ..., n-1} has n elements. We
prove this by induction on n: removing the largest element n-1 leaves
{0, 1, ..., n-2} with n-1 elements.\"
"

/-- `Finset.range_add_one` states that
`Finset.range (n + 1) = insert n (Finset.range n)`.

The range of `n + 1` is obtained by inserting `n` into `range n`. -/
TheoremDoc Finset.range_add_one as "Finset.range_add_one" in "Finset"

NewTheorem Finset.range_add_one
DisabledTactic trivial decide native_decide aesop simp_all simp
DisabledTheorem Finset.card_range
