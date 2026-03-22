import Game.Metadata

World "MeetFin"
Level 17

Title "Two Elements"

Introduction "
# Case Analysis on Fin 2

`Fin 2` has two elements: `0` and `1`. To prove something about an
arbitrary `x : Fin 2`, you can **case-split**: handle each possible
value of `x` separately.

In Level 16, you learned to destructure a `Fin` element with
`cases x with | mk v hlt`. Now you'll take the next step:
**case-splitting on the natural number** to handle each value.

After destructuring, `v : ℕ` and `hlt : v < 2`. Use
`cases v with | zero | succ n` to split into two goals:
- `v = 0`: the element is `0`, close with `left; rfl`
- `v = n + 1`: split again on `n`
  - `n = 0`: the element is `1`, close with `right; rfl`
  - `n = succ m`: now `v ≥ 2`, contradicting `hlt : v < 2`

For the impossible case, you'll use a new tactic: `absurd`.
`absurd h1 h2` closes a goal when `h1 : P` and `h2 : ¬P`. Here,
`hlt` says `v < 2` but `v ≥ 2`, so `exact absurd hlt (by omega)` works.

**Your task**: Prove that every element of `Fin 2` is either `0` or `1`.
"

/-- Every element of `Fin 2` is either `0` or `1`. -/
Statement (x : Fin 2) : x = 0 ∨ x = 1 := by
  Hint "Start by destructuring `x` into its components:
  `cases x with | mk v hlt`"
  cases x with
  | mk v hlt =>
  Hint "Now `v : ℕ` and `hlt : v < 2`. Case-split on `v`:
  `cases v with | zero | succ n`"
  cases v with
  | zero =>
    Hint "In this case `v = 0`, so `x` is the element `0`.
    Choose the left disjunct with `left`, then close with `rfl`."
    left
    rfl
  | succ n =>
    Hint "Now `v = n + 1`. Case-split once more on `n` to determine
    whether `v = 1` or `v ≥ 2`:
    `cases n with | zero | succ m`"
    cases n with
    | zero =>
      Hint "Now `v = 1`. Choose the right disjunct with `right`,
      then close with `rfl`."
      right
      rfl
    | succ m =>
      Hint (hidden := true) "Here `v = m + 2`, but `hlt` says `v < 2`.
      This is impossible — `exact absurd hlt (by omega)` closes it."
      exact absurd hlt (by omega)

Conclusion "
You've just performed **exhaustive case analysis** on `Fin 2`.

The strategy — which we'll call **Fin case analysis** — is:
1. **Destructure** the `Fin` element: `cases x with | mk v hlt` (Level 16)
2. **Case-split** on the natural number: `cases v with | zero | succ n`
3. **Handle** each case: valid cases with `left`/`right` + `rfl`,
   impossible cases with `absurd` + `omega`

**Why does this work?** Exhaustive case analysis on `Fin n` terminates
because `.isLt` bounds the natural number. Each `cases` step peels
off one possible value (0, then 1, then 2, ...), and the `.isLt`
bound ensures that after `n` valid cases, the remaining case is
impossible — the value would need to be ≥ `n`, contradicting `v < n`.
This is the **Fin contradiction pattern** from Level 13 applied to the
impossible branch. This termination is what makes `Fin n` a *finite*
type in a proof-relevant sense: you can enumerate all elements and
handle each one. This idea will be formalized as `Fintype` in a later
world.

This strategy works for any `Fin n` by nesting enough `cases` on the
natural number. But imagine doing this for `Fin 100`: you'd need 100
branches, 99 of which are contradiction proofs. The `fin_cases` tactic
(currently disabled) automates all of this — it performs the case split
and handles the impossible branches automatically. You'll unlock it
later.

Fun fact: `Fin 2` is equivalent to `Bool` — both have exactly two
elements. Where `Bool` has `true` and `false`, `Fin 2` has `0` and `1`.

**A note on `absurd`**: You used `absurd` here for a *bound violation*
in case analysis — the value was too large for the bound. This is a
general tool you'll use in later worlds whenever you have contradictory
hypotheses. In the next level, you'll practice case analysis on `Fin 3`,
and after that you'll learn a different pattern (`intro h; cases h`)
for when *constructors themselves* don't match (like `0 = 1`).
"

/-- `absurd` closes a goal when you have contradictory hypotheses.

## Syntax
```
exact absurd h1 h2
```
where `h1 : P` and `h2 : ¬P` (or `h1 : ¬P` and `h2 : P`).

## When to use it
When you have a proposition and its negation in your hypotheses,
or when you can derive one of them from context.

## Example
```
-- hlt : v < 2
-- But v = m + 2, so v < 2 is impossible
exact absurd hlt (by omega)
```

## Note
`absurd` is the formal version of proof by contradiction:
if you can show both `P` and `¬P`, the current goal is closed.
-/
TacticDoc absurd

NewTactic absurd

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Fin.forall_fin_two
