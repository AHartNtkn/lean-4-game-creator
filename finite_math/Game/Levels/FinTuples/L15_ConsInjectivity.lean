import Game.Metadata

World "FinTuples"
Level 15

Title "Cons Injectivity"

Introduction "
# Fin.cons Determines Its Inputs

You've learned how to *read* a cons'd tuple using the access
lemmas: `Fin.cons_val_zero` and `Fin.cons_val_succ`. Now let's
prove the converse: **if two cons'd tuples are equal, their
heads and tails must be equal**.

This is the *injectivity* of `Fin.cons`: no information is lost
when you prepend. If `Fin.cons a f = Fin.cons b g`, then `a = b`
and `f = g`.

**New tool: `congrFun`**. If `h : f = g`, then `congrFun h a`
gives you `f a = g a` — the functions agree at input `a`. This
is the **pointwise extraction** move.

**Strategy**:
For the head: `have h0 := congrFun h 0` extracts agreement at
index `0`, then simplify with `Fin.cons_val_zero`.
For the tail: `ext i`, then `have hi := congrFun h i.succ`
extracts agreement at `i.succ`, then simplify with
`Fin.cons_val_succ`.

**Your task**: Prove that `Fin.cons` is injective.
"

/-- If two cons'd tuples are equal, their heads and tails match. -/
Statement (a b : ℕ) (f g : Fin 2 → ℕ)
    (h : (Fin.cons a f : Fin 3 → ℕ) = Fin.cons b g) :
    a = b ∧ f = g := by
  Hint "Use `constructor` to split into two goals: heads equal
  and tails equal."
  constructor
  · -- heads are equal
    Hint "Extract what `h` says at index `0`:
    `have h0 := congrFun h 0`.
    This gives `h0 : (Fin.cons a f) 0 = (Fin.cons b g) 0`."
    Hint (hidden := true) "`have h0 := congrFun h 0`"
    have h0 := congrFun h 0
    Hint "Now simplify both sides using the access lemma:
    `rw [Fin.cons_val_zero, Fin.cons_val_zero] at h0`"
    rw [Fin.cons_val_zero, Fin.cons_val_zero] at h0
    Hint "Now `{h0}` is exactly the goal. Use `exact h0`."
    exact h0
  · -- tails are equal
    Hint "Use `ext i` to reduce function equality to pointwise
    equality."
    ext i
    Hint "Extract agreement at index `i.succ`:
    `have hi := congrFun h i.succ`."
    Hint (hidden := true) "`have hi := congrFun h i.succ`"
    have hi := congrFun h i.succ
    Hint (hidden := true) "`rw [Fin.cons_val_succ, Fin.cons_val_succ] at hi`
    then `exact hi`"
    rw [Fin.cons_val_succ, Fin.cons_val_succ] at hi
    exact hi

NewTheorem congrFun

Conclusion "
`Fin.cons` is **injective**: equal outputs mean equal inputs.
The proof pattern uses **pointwise extraction** via `congrFun`:

1. `have h0 := congrFun h 0` — extract agreement at a specific index
2. Simplify with the access lemma to relate inputs
3. For the tail, use `ext` to reduce to pointwise equality first

`congrFun` is the clean way to go from a function equality
`h : f = g` to a value equality `f a = g a` at a specific input.

The same idea works for `vecSnoc`: if `vecSnoc f x = vecSnoc g y`,
then `x = y` (extract at `Fin.last`) and `f = g`
(extract at `i.castSucc`). You'll prove this in the next level.

Note: the boss level tests different abilities (reconstruction
strategies and index-by-index verification), not injectivity proofs.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
