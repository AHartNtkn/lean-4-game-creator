import Game.Metadata

World "FinTuples"
Level 16

Title "Snoc Injectivity"

Introduction "
# vecSnoc Determines Its Inputs

In Level 15, you proved that `Fin.cons` is injective: equal
cons'd tuples have equal heads and tails. The same holds for
`vecSnoc` — and the proof is the dual, using `vecSnoc_last`
and `vecSnoc_castSucc` instead of `Fin.cons_val_zero` and
`Fin.cons_val_succ`.

If `vecSnoc f x = vecSnoc g y`, then:
- `x = y` — the appended elements are equal (evaluate at `Fin.last`)
- `f = g` — the original tuples are equal (evaluate at `i.castSucc`)

**Strategy**: The same `congrFun` pattern as cons injectivity:
1. `have hl := congrFun h (Fin.last 2)` — extract agreement
2. Simplify with the access lemma (`vecSnoc_last` or `vecSnoc_castSucc`)
3. For `f = g`, use `ext i` first

**Your task**: Prove that `vecSnoc` is injective.
"

/-- If two snoc'd tuples are equal, their tails and last elements match. -/
Statement (x y : ℕ) (f g : Fin 2 → ℕ)
    (h : (vecSnoc f x : Fin 3 → ℕ) = vecSnoc g y) :
    x = y ∧ f = g := by
  Hint "Use `constructor` to split into two goals: last elements
  equal and original tuples equal."
  constructor
  · -- last elements are equal
    Hint "Extract agreement at `Fin.last 2` — the last position:
    `have hl := congrFun h (Fin.last 2)`."
    Hint (hidden := true) "`have hl := congrFun h (Fin.last 2)`"
    have hl := congrFun h (Fin.last 2)
    Hint "Now simplify both sides using the access lemma:
    `rw [vecSnoc_last, vecSnoc_last] at hl`"
    rw [vecSnoc_last, vecSnoc_last] at hl
    Hint "Now `hl` is exactly the goal. Use `exact hl`."
    exact hl
  · -- original tuples are equal
    Hint "Use `ext i` to reduce function equality to pointwise
    equality."
    ext i
    Hint "Extract agreement at `i.castSucc`:
    `have hi := congrFun h i.castSucc`."
    Hint (hidden := true) "`have hi := congrFun h i.castSucc`"
    have hi := congrFun h i.castSucc
    Hint (hidden := true) "`rw [vecSnoc_castSucc, vecSnoc_castSucc] at hi`
    then `exact hi`"
    rw [vecSnoc_castSucc, vecSnoc_castSucc] at hi
    exact hi

Conclusion "
`vecSnoc` is **injective**: equal outputs mean equal inputs.
The proof uses `congrFun` for pointwise extraction, just like
the cons version — the duality extends to their injectivity proofs:

| | Cons | Snoc |
|---|---|---|
| Head/last equal | `congrFun h 0` | `congrFun h (Fin.last 2)` |
| Access lemma | `Fin.cons_val_zero` | `vecSnoc_last` |
| Tail/init equal | `congrFun h i.succ` | `congrFun h i.castSucc` |
| Access lemma | `Fin.cons_val_succ` | `vecSnoc_castSucc` |

Both use the same pattern: `congrFun` → access lemma → conclude.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
