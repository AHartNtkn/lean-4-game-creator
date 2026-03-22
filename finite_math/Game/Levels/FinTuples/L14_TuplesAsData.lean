import Game.Metadata

World "FinTuples"
Level 14

Title "Tuples as Data"

Introduction "
# Tuples Represent Real Data

So far, every exercise has been about structural properties of
tuples: how `cons` and `tail` relate, how `ext` proves equality.
Now you'll see tuples used as **data** — specifically, as vectors
whose entries you can compute with.

The tuple `![1, 0]` can represent a 2D vector. The tuple
`![2, 3]` is another. Their **componentwise sum** — adding
corresponding entries — should give `![3, 3]`:

| Index | `![1, 0]` | `![2, 3]` | Sum |
|---|---|---|---|
| 0 | 1 | 2 | 3 |
| 1 | 0 | 3 | 3 |

In Lean, componentwise sum is expressed as a function:
`fun i => v i + w i` — at each index `i`, add the entries.

**Reading the goal**: The statement looks dense because it spells out
the type annotations: `(![1, 0] : Fin 2 -> NN)`. Read it as:
'the function that maps index `i` to `v[i] + w[i]` equals `![3, 3]`.'
The type annotations are just Lean being explicit about the types.

**Your task**: Prove that the componentwise sum of `![1, 0]`
and `![2, 3]` equals `![3, 3]`.

**Strategy**: Use `ext` to reduce to pointwise equality, then
case-split on the index and verify each entry with `rfl`.
"

/-- Componentwise addition of two concrete vectors. -/
Statement : (fun i : Fin 2 => (![1, 0] : Fin 2 → ℕ) i + (![2, 3] : Fin 2 → ℕ) i) = ![3, 3] := by
  Hint "Use `ext ⟨v, hv⟩` to reduce function equality to
  pointwise equality."
  ext ⟨v, hv⟩
  Hint "Now verify each index. Case-split on `v`."
  Hint (hidden := true) "`cases v with | zero => rfl | succ n => ...`
  and continue splitting on `n`."
  cases v with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ k => exact absurd hv (by omega)

Conclusion "
This is the promise of `Fin n -> alpha` delivered: tuples are
not just abstract functions — they represent **vectors**, and
you can prove facts about componentwise operations on them.

The proof used the same `ext` + case split pattern as Level 13,
but now applied to a computation with mathematical meaning:
vector addition.

In later worlds, you'll see this pattern generalized:
- **Finset.image** applies a function to every element of a set
  (the set-level version of tuple transformation)
- **Big operators** (`\\sum`, `\\prod`) aggregate tuple entries
  (the formal version of 'sum all components')
- **Matrices** are tuples of tuples (`Fin n -> Fin m -> alpha`),
  and matrix multiplication is built from componentwise
  operations like the one you just verified

**Looking ahead**: How many 3-bit binary strings are there? A binary
string of length 3 is a tuple `Fin 3 -> Bool`, and the Fintype world
will give you the tools to answer: `Fintype.card (Fin 3 -> Bool) = 2^3 = 8`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
