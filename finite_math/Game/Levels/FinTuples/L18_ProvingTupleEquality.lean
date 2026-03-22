import Game.Metadata

World "FinTuples"
Level 18

Title "Proving Tuple Equality"

Introduction "
# Identifying a Tuple from Its Values

Suppose you know the value of `f` at every index:
`f 0 = 1`, `f 1 = 4`, `f 2 = 9`. Can you conclude that
`f = ![1, 4, 9]`?

Yes — by function extensionality. The strategy:

1. `ext` to reduce `f = ![1, 4, 9]` to `f i = ![1, 4, 9] i`
2. Case-split on `i` to handle each index separately
3. At each concrete index, use the corresponding hypothesis
   and the fact that `![1, 4, 9]` reduces by definition

The case split is the same nested `cases` pattern you used
in MeetFin for `Fin 3`. After destructuring `i` as `⟨v, hv⟩`,
split on `v`: the cases `0`, `1`, `2` correspond to the three
hypotheses, and the impossible case `v ≥ 3` is closed by
`absurd hv (by omega)`.

**Your task**: Given the values of `f` at each index, prove
`f = ![1, 4, 9]`.
"

/-- A function is determined by its values at each index. -/
Statement (f : Fin 3 → ℕ)
    (h0 : f 0 = 1) (h1 : f 1 = 4) (h2 : f 2 = 9) :
    f = ![1, 4, 9] := by
  Hint "To show two functions are equal, check them index by index.
  Use `ext ⟨v, hv⟩` to introduce the index and
  reduce to `f ⟨v, hv⟩ = ![1, 4, 9] ⟨v, hv⟩`."
  ext ⟨v, hv⟩
  Hint "Now case-split on `v` with `cases v with | zero | succ n`.
  The `zero` case corresponds to index 0."
  cases v with
  | zero =>
    Hint "The goal is `f 0 = ![1, 4, 9] 0`, which simplifies to `f 0 = 1`.
    You have `{h0} : f 0 = 1`. Use `exact h0`."
    exact h0
  | succ n =>
    Hint (hidden := true) "Continue splitting: `cases n with | zero | succ m`"
    cases n with
    | zero =>
      Hint (hidden := true) "The goal is `f 1 = 4`. Use `exact h1`."
      exact h1
    | succ m =>
      Hint (hidden := true) "Split once more on `m`."
      cases m with
      | zero =>
        Hint (hidden := true) "The goal is `f 2 = 9`. Use `exact h2`."
        exact h2
      | succ k =>
        Hint (hidden := true) "Here `v = k + 3` but `hv` says `v < 3`.
        Impossible: `exact absurd hv (by omega)`."
        exact absurd hv (by omega)

Conclusion "
The `ext` + case split pattern is the standard way to prove
a function from `Fin n` equals a specific tuple:

```
ext ⟨v, hv⟩
cases v with | zero | succ n
-- in the zero branch: handle index 0
-- in the succ branch:
  cases n with | zero | succ m
  -- zero: handle index 1
  -- succ: handle index 2, etc.
```

The impossible branch (where `v ≥ n`) is always closed by
`exact absurd hv (by omega)`.

This pattern scales to any `Fin n`, though it gets verbose
for large `n`. (Later, you'll learn tactics like `fin_cases`
that automate this case split.)
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
