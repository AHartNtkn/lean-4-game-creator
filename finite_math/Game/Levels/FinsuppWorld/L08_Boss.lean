import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 8

Title "Boss: A Finsupp reasoning chain"

Introduction
"
# Boss: A Complete `Finsupp` Reasoning Chain

Time to put everything together. You will work with `Finsupp.single 2 7`
and prove three facts:

1. **Evaluation** (L1-L2): `f 2 = 7`.
2. **Support** (L3): `f.support = {2}`.
3. **Summation** (L6): `f.sum (fun a m => a * m) = 14`.

## Strategy

Each part uses a different skill from this world:

| Part | Key lemma | Seeded in |
|------|-----------|-----------|
| 1 | `Finsupp.single_apply` + `if_pos` | L1, L2 |
| 2 | `Finsupp.support_single_ne_zero` | L3 |
| 3 | `Finsupp.sum_single_index` | L6 |

The third part is a small twist: the function `fun a m => a * m`
weights the value by its index, so `h 2 7 = 2 * 7 = 14`. The side
condition `h 2 0 = 0` becomes `2 * 0 = 0`, which is proved by `ring`.

## Your task

Prove the conjunction of all three parts.
"

/-- Three facts about `Finsupp.single 2 7`: evaluation, support, and sum. -/
Statement : (Finsupp.single 2 (7 : ℕ)) 2 = 7 ∧
    (Finsupp.single 2 (7 : ℕ)).support = {2} ∧
    (Finsupp.single 2 (7 : ℕ)).sum (fun a m => a * m) = 14 := by
  Hint "Start with `refine ⟨?_, ?_, ?_⟩` to split into three goals.
  (Or use `constructor` twice.)"
  refine ⟨?_, ?_, ?_⟩
  · Hint "**Part 1**: Evaluate `f 2`. Recall `f = single 2 7`.
    Use `Finsupp.single_apply` and `if_pos rfl`."
    Hint (hidden := true) "Try `rw [Finsupp.single_apply, if_pos rfl]`."
    rw [Finsupp.single_apply, if_pos rfl]
  · Hint "**Part 2**: Compute the support. Use `Finsupp.support_single_ne_zero`.
    You need to supply the point `2` and a proof that `7 ≠ 0`."
    Hint (hidden := true) "Try `exact Finsupp.support_single_ne_zero 2 (by omega)`."
    exact Finsupp.support_single_ne_zero 2 (by omega)
  · Hint "**Part 3**: Compute `f.sum (fun a m => a * m)`.
    Use `Finsupp.sum_single_index`. The side condition `(fun a m => a * m) 2 0 = 0`
    simplifies to `2 * 0 = 0`, which `ring` can close.

    So use `rw [Finsupp.sum_single_index (by ring)]`."
    Hint (hidden := true) "Try `rw [Finsupp.sum_single_index (by ring)]`."
    rw [Finsupp.sum_single_index (by ring)]

Conclusion
"
Congratulations on completing the **Finitely Supported Functions** world!

You proved evaluation, support, and summation for a `Finsupp.single` in
a single proof, integrating the core skills from this world.

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| `Finsupp` definition and evaluation | L01 | `Finsupp.single_apply` |
| Two-case evaluation (`if_pos`/`if_neg`) | L02 | `Finsupp.single_apply` |
| Support of a `Finsupp` | L03 | `Finsupp.support`, `support_single_ne_zero` |
| Building multi-point `Finsupp`s | L04 | `Finsupp.add_apply` |
| Totality: `Finsupp` ≠ partial function | L05 | `mem_support_iff` |
| `Finsupp.sum` and `sum_single_index` | L06 | `Finsupp.sum` |
| `sum_add_index'` for sums of `Finsupp`s | L07 | `Finsupp.sum_add_index'` |
| Integration | L08 | All of the above |

## Transfer moment

In ordinary mathematics, a finitely supported function is just a function
that is nonzero at finitely many points. You write things like:
\"Let $f : S \\to R$ have finite support\" and then freely evaluate $f$,
compute its support, and sum over the support.

In Lean, `Finsupp` bundles all of this into a single type: the function,
the support (as a `Finset`), and the proof that they agree. The API
(`single_apply`, `support_single_ne_zero`, `sum_single_index`,
`sum_add_index'`) formalizes the basic manipulations you would do on paper.

The key difference: in ordinary math, finiteness of the support is
an *assumption* you carry around. In Lean, it is *built into the type*.

## What comes next

Finitely supported functions are the foundation for:
- **Polynomials** (as `Finsupp ℕ R` with a ring structure),
- **Free modules** (as `Finsupp S R` with a module structure),
- **Formal sums** in combinatorics and homological algebra.

The next worlds explore permutations of finite types, and further
applications of finite structures.
"

TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
