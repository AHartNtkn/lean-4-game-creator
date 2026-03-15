import GameServer.Commands
import Mathlib

World "FinIntro"
Level 13

Title "Boss: castSucc and last are disjoint"

Introduction
"
# Boss Level: The image of `castSucc` misses `last`

Time to integrate what you have learned.

In this world, you discovered that `Fin (n + 1)` is partitioned into:
- The image of `Fin.castSucc` (values `0, ..., n - 1`)
- The single point `Fin.last n` (value `n`)

These two parts are disjoint: no element in the image of `castSucc` equals
`Fin.last n`. Your task is to prove this for a specific case.

## Your task

Given `i : Fin 4`, prove that `Fin.castSucc i ≠ Fin.last 4`.

This requires combining several skills from this world:
1. **`intro h`** -- assume for contradiction that they are equal
2. **`have hv : i.val = 4 := congr_arg Fin.val h`** -- extract the value-level
   consequence. You practiced `congr_arg` in the previous level! Here, Lean
   checks that `(Fin.castSucc i).val` reduces to `i.val` and `(Fin.last 4).val`
   reduces to `4` by definition, so the type annotation `i.val = 4` matches.
3. **`omega`** -- derive a contradiction: `hv : i.val = 4` but `i.isLt : i.val < 4`

The key insight: `Fin.castSucc i` has value `i.val` (which is `< 4`),
while `Fin.last 4` has value `4`. If they were equal, we would need
`i.val = 4`, contradicting the bound.

There is no new material -- only integration.
"

/-- `Fin.castSucc i` is never equal to `Fin.last n`. -/
Statement (i : Fin 4) : Fin.castSucc i ≠ Fin.last 4 := by
  Hint "Start by assuming the opposite. Try `intro h`."
  intro h
  Hint "Now `h : Fin.castSucc i = Fin.last 4`. Extract the value-level equality
  using `congr_arg` as you did in the previous level.
  Try `have hv : i.val = 4 := congr_arg Fin.val h`."
  have hv : i.val = 4 := congr_arg Fin.val h
  Hint "Now `hv : i.val = 4` and `i.isLt : i.val < 4`. These contradict
  each other. Try `omega`."
  omega

/-- `Fin.castSucc_ne_last` states that `Fin.castSucc i ≠ Fin.last n` for any `i : Fin n`.
This is disabled in this level so you practice the proof yourself. -/
TheoremDoc Fin.castSucc_ne_last as "Fin.castSucc_ne_last" in "Fin"

/-- `Fin.castSucc_lt_last` states that `Fin.castSucc i < Fin.last n` for any `i : Fin n`.
This is disabled in this level so you practice the proof yourself. -/
TheoremDoc Fin.castSucc_lt_last as "Fin.castSucc_lt_last" in "Fin"

/-- `ne_of_lt` derives `a ≠ b` from `a < b`. This is disabled in this level
so you practice the proof from first principles. -/
TheoremDoc ne_of_lt as "ne_of_lt" in "Order"

DisabledTheorem Fin.castSucc_ne_last Fin.castSucc_lt_last ne_of_lt

Conclusion
"
Congratulations on completing the first world!

You proved that `Fin.castSucc` and `Fin.last` never collide -- they
partition `Fin (n + 1)` into two disjoint pieces. This structural
fact is the basis for induction on finite types: to define a function
on `Fin (n + 1)`, handle the `castSucc` cases and the `last` case
separately.

## What you learned

1. **`Fin n`** is the type of natural numbers less than `n`
2. **`Fin.mk`** constructs elements; `⟨val, proof⟩` is shorthand
3. **`Fin.val`** (or `↑`) extracts the underlying natural number
4. **`Fin.isLt`** provides the proof that the value is in bounds
5. **Subtype extensionality** -- two `Fin` elements are equal iff their values are
6. **`Fin 0`** is empty; **`Fin 1`** is a singleton
7. **`Fin.last n`** is the largest element of `Fin (n + 1)` with value `n`
8. **`Fin.castSucc`** embeds `Fin n` into `Fin (n + 1)` preserving the value
9. **`Fin.succ`** maps `Fin n` into `Fin (n + 1)` by incrementing the value
10. **`congr_arg`** extracts consequences from equalities by applying a function

## Transfer to paper proofs

The proof you just wrote says:

\"Suppose $\\text{castSucc}(i) = \\text{last}$. Then their values are equal:
$i = n$. But $i < n$ since $i \\in \\text{Fin}\\, n$. Contradiction.\"

This is a standard proof by contradiction. The `intro h` step is
\"suppose for contradiction,\" `congr_arg Fin.val h` extracts the
value-level consequence, and `omega` derives the contradiction from
the arithmetic. Each tactic step corresponds to a sentence in the
paper proof -- this is the structure you should internalize.

## What's next

In the next world, you will learn `fin_cases` and `decide`, which let you
verify properties of `Fin n` by checking all cases explicitly. Later in
the course, you will see that sums over `Finset.range n` are intimately
connected to `Fin n` -- each element of `range n` corresponds to an element
of `Fin n`.
"
