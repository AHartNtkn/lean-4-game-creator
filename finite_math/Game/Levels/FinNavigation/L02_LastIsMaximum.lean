import Game.Metadata

World "FinNavigation"
Level 2

Title "Last is the Maximum"

Introduction "
# Using Fin.val_last as a Rewrite

`Fin.val_last` isn't just for computing concrete values — it's a
**rewrite** tool. When you have `(Fin.last n).val` somewhere in
your goal, `rw [Fin.val_last]` replaces it with `n`, often
unlocking `omega` to finish the job.

**Your task**: Prove that every element of `Fin 5` has value at
most `(Fin.last 4).val`.

Strategy:
1. `intro i` to name the element
2. `rw [Fin.val_last]` to simplify the right side to `4`
3. `omega` to close `i.val ≤ 4` (since `i.val < 5`)
"

/-- Every element of `Fin 5` has value at most `(Fin.last 4).val`. -/
Statement : ∀ i : Fin 5, i.val ≤ (Fin.last 4).val := by
  Hint "Start with `intro i` to name the element."
  intro i
  Hint "Now `rw [Fin.val_last]` converts `(Fin.last 4).val` to `4`."
  rw [Fin.val_last]
  Hint "The goal is `i.val ≤ 4`. Since `i : Fin 5`, you know
  `i.val < 5`, so `i.val ≤ 4`. `omega` handles this."
  omega

Conclusion "
The **rewrite-then-omega** pattern will be your main tool in this
world:

1. Use a val lemma (`Fin.val_last`, or the ones you'll learn next)
   to simplify `Fin` expressions to plain natural numbers
2. Use `omega` to close the resulting arithmetic goal

Why is `Fin.last` the maximum? Because every `i : Fin (n+1)`
satisfies `i.val < n+1`, which means `i.val ≤ n`. And
`(Fin.last n).val = n`. So `i.val ≤ (Fin.last n).val`.

In plain math: $\\forall\\, i \\in \\{0, \\ldots, n\\},\\; i \\leq n$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos Fin.le_last
