import Game.Metadata

World "FinTuples"
Level 9

Title "Appending with vecSnoc"

Introduction "
# vecSnoc: Adding to the End

`Fin.cons` prepends an element at the *beginning* of a tuple.
What about adding an element at the *end*?

**`vecSnoc f x`** takes:
- A tuple `f : Fin n → α`
- An element `x : α`

and produces `vecSnoc f x : Fin (n + 1) → α` — the tuple `f`
with `x` appended at the end.

The access lemmas are:
- `vecSnoc f x (Fin.last n) = x` — the last element is `x`
- `vecSnoc f x i.castSucc = f i` — earlier elements are from `f`

Notice the connection to FinNavigation: `Fin.cons` routes through
`0` / `succ` (the successor decomposition), while `vecSnoc` routes
through `castSucc` / `last` (the other decomposition you learned).
These are **dual constructions** — one builds from the front,
the other from the back.

**Your task**: Prove both access lemmas for `vecSnoc`.
"

/-- The access lemmas for vecSnoc. -/
Statement (a : ℕ) (f : Fin 2 → ℕ) :
    vecSnoc f a (Fin.last 2) = a ∧
    ∀ i : Fin 2, vecSnoc f a i.castSucc = f i := by
  Hint "Use `constructor` to split the conjunction."
  constructor
  · Hint "The goal is `vecSnoc f a (Fin.last 2) = a`.
    Use `exact vecSnoc_last f a`."
    exact vecSnoc_last f a
  · Hint "Start with `intro i`, then use
    `exact vecSnoc_castSucc f a i`."
    intro i
    exact vecSnoc_castSucc f a i

Conclusion "
You now have two ways to build tuples:

| Operation | Adds where | Routes through |
|---|---|---|
| `Fin.cons a f` | Beginning | `0` / `succ` |
| `vecSnoc f x` | End | `castSucc` / `last` |

The duality is exact:
- `Fin.cons` uses the **0/succ decomposition** from FinNavigation:
  every `Fin (n+1)` element is either `0` or `i.succ`
- `vecSnoc` uses the **castSucc/last decomposition**:
  every `Fin (n+1)` element is either `i.castSucc` or `Fin.last n`

This is the payoff from learning both decompositions in
FinNavigation — they power the two dual tuple constructors.
"

/-- `vecSnoc f x` appends element `x` to the end of tuple `f`,
producing a tuple of length `n + 1`.

## Syntax
```
vecSnoc f x    -- append x to the end of f
```

## Type
`vecSnoc : (Fin n → α) → α → Fin (n + 1) → α`

## Element access
- `vecSnoc f x (Fin.last n) = x` — `vecSnoc_last`
- `vecSnoc f x i.castSucc = f i` — `vecSnoc_castSucc`

## Example
`vecSnoc ![10, 20] 30 = ![10, 20, 30]`
-/
DefinitionDoc vecSnoc as "vecSnoc"

/-- `vecSnoc_last f x` states that `vecSnoc f x (Fin.last n) = x`.

The last element of a snoc'd tuple is the appended element.
-/
TheoremDoc vecSnoc_last as "vecSnoc_last" in "Fin"

/-- `vecSnoc_castSucc f x i` states that `vecSnoc f x i.castSucc = f i`.

The earlier elements of a snoc'd tuple come from the original tuple.
-/
TheoremDoc vecSnoc_castSucc as "vecSnoc_castSucc" in "Fin"

NewDefinition vecSnoc
NewTheorem vecSnoc_last vecSnoc_castSucc

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
