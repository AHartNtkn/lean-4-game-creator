import Game.Metadata

World "FinNavigation"
Level 10

Title "The Other Decomposition"

Introduction "
# The 0/succ Decomposition

In Levels 1-9, you studied the **castSucc/last** path:
separation (Level 7), injectivity (Level 8), and the dual
`succ` injectivity (Level 9). Now for the second decomposition.
every element of `Fin (n+1)` is either `Fin.last n` or
`j.castSucc` for some `j : Fin n`.

There is a **dual decomposition**: every element of `Fin (n+1)`
is either `0` or `j.succ` for some `j : Fin n`.

Why? An element `i : Fin (n+1)` has value `v` in
$\\{0, 1, \\ldots, n\\}$. If `v = 0`, then `i = 0`. If `v >= 1`,
then `v = (v-1) + 1`, so `i = j.succ` where
`j = ⟨v-1, ...⟩ : Fin n`.

These two decompositions are **dual**:

| Decomposition | Cases | Uses |
|---|---|---|
| castSucc/last | `i = j.castSucc` or `i = Fin.last n` | Appending (vecSnoc) |
| 0/succ | `i = 0` or `i = j.succ` | Prepending (Fin.cons) |

In the next world, you'll see how `Fin.cons` uses the 0/succ
decomposition: the head goes to index `0`, and the tail goes
to the `succ` indices.

**Your task**: Prove the 0/succ decomposition for `Fin 3`.
The strategy is the same case analysis pattern: destructure,
split on the value, handle each case.
"

/-- Every element of Fin 3 is either 0 or a successor. -/
Statement : ∀ i : Fin 3, i = 0 ∨ ∃ j : Fin 2, i = j.succ := by
  Hint "Start with `intro i`, then destructure:
  `cases i with | mk v hv`."
  intro i
  Hint (hidden := true) "`cases i with | mk v hv`"
  cases i with
  | mk v hv =>
  Hint "Now case-split on `v`: is the value `0` or `succ n`?"
  Hint (hidden := true) "`cases v with | zero | succ n`"
  cases v with
  | zero =>
    Hint "Here `v = 0`, so `i = 0`. Choose `left` and use `rfl`."
    left
    rfl
  | succ n =>
    Hint "Here `v = n + 1`, so `i = j.succ` where
    `j = ⟨n, ...⟩ : Fin 2`. Choose `right`, provide the witness,
    then prove the equality."
    right
    Hint (hidden := true) "`use ⟨n, by omega⟩`"
    use ⟨n, by omega⟩
    Hint (hidden := true) "Use `ext` to reduce to values,
    then `rw [Fin.val_succ]`."
    ext
    rw [Fin.val_succ]

Conclusion "
You've proved the **0/succ decomposition**: every element of
`Fin (n+1)` is either `0` (the minimum) or `j.succ` for some
`j : Fin n` (a shifted element).

Combined with the **castSucc/last decomposition** from Levels 1-8,
you now have two ways to partition `Fin (n+1)`:

| Decomposition | Singleton | Image |
|---|---|---|
| castSucc/last | `Fin.last n` (value $n$) | `j.castSucc` (values $0, \\ldots, n-1$) |
| 0/succ | `0` (value $0$) | `j.succ` (values $1, \\ldots, n$) |

The duality is: castSucc/last splits off the *maximum*;
0/succ splits off the *minimum*.

This dual structure is the reason tuples can be built from either
end: `Fin.cons` routes through `0`/`succ`, and `vecSnoc` routes
through `castSucc`/`last`.

**Connection to natural number induction**: The 0/succ decomposition
says `Fin (n+1)` has the same recursive structure as `NN`: every
element is either `0` or the successor of something smaller. This
IS the induction principle for `Fin` — and it's why `Fin.cons`
(which handles `0` and `succ` separately) is the natural way to
define functions on `Fin (n+1)`, just as recursion on `0` and
`succ` is the natural way to define functions on `NN`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem Fin.eq_zero_or_eq_succ Fin.cases
