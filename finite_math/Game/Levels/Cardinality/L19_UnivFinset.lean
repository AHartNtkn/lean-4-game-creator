import Game.Metadata

World "Cardinality"
Level 19

Title "The Universal Finset"

Introduction "
# Finset.univ: All Elements of a Finite Type

So far, your finsets have been built by hand: `insert`, `singleton`,
`range`, `filter`, `image`. But for a finite type like `Fin n`, there's
a finset that contains **all** elements: `Finset.univ`.

`Finset.univ : Finset (Fin n)` — the finset of every element of `Fin n`.

Two key facts connect `univ` to cardinality:

- `Finset.card_univ : (Finset.univ : Finset α).card = Fintype.card α`
  — the size of `univ` equals the type's cardinality
- `Fintype.card_fin n : Fintype.card (Fin n) = n`
  — the type `Fin n` has exactly `n` elements

Chaining these: `(Finset.univ : Finset (Fin 5)).card = 5`.

**Your task**: Prove that `Finset.univ` for `Fin 5` has exactly 5 elements.
"

/-- The universal finset of Fin 5 has 5 elements. -/
Statement : (Finset.univ : Finset (Fin 5)).card = 5 := by
  Hint "Use `Finset.card_univ` to convert the univ cardinality to
  `Fintype.card (Fin 5)`, then `Fintype.card_fin` to get `5`."
  Hint (hidden := true) "Try `rw [Finset.card_univ, Fintype.card_fin]`."
  rw [Finset.card_univ, Fintype.card_fin]

Conclusion "
`Finset.univ` is the finset counterpart of 'the entire type.'

| Tool | What it says |
|---|---|
| `Finset.univ` | The finset of all elements of a finite type |
| `Finset.card_univ` | `(Finset.univ).card = Fintype.card α` |
| `Fintype.card_fin n` | `Fintype.card (Fin n) = n` |

Together: `(Finset.univ : Finset (Fin n)).card = n`. This connects
the finset world (where you count elements of a set) to the type world
(where you count elements of a type).

The next level introduces `Finset.subset_univ` — the fact that every
finset of a finite type is contained in `univ`. Combined with
`card_le_card`, this gives cardinality upper bounds.
"

/-- `Finset.univ` is the finset of all elements of a finite type.

For `Fin n`, `Finset.univ` contains all `n` elements.

## Example
```
Finset.univ : Finset (Fin 3) -- contains 0, 1, 2
```
-/
DefinitionDoc Finset.univ as "Finset.univ"

NewDefinition Finset.univ

/-- `Finset.card_univ` states that `(Finset.univ : Finset α).card = Fintype.card α`:
the cardinality of the universal finset equals the type's cardinality. -/
TheoremDoc Finset.card_univ as "Finset.card_univ" in "Card"

/-- `Fintype.card_fin n` states that `Fintype.card (Fin n) = n`:
the type `Fin n` has exactly `n` elements. -/
TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Card"

/-- `Finset.mem_univ x` states that every element `x` of a finite type
belongs to `Finset.univ`. This is always true — `univ` contains everything. -/
TheoremDoc Finset.mem_univ as "Finset.mem_univ" in "Card"

NewTheorem Finset.card_univ Fintype.card_fin Finset.mem_univ

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.card_le_univ Finset.eq_univ_of_card
