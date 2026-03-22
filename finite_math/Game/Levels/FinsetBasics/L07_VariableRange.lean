import Game.Metadata

World "FinsetBasics"
Level 7

Title "Variable Range Membership"

Introduction "
# The Bridge from Fin to Finset

In Level 4, you proved `3 ∈ Finset.range 5` using concrete numbers.
In Level 5, you proved `5 ∉ Finset.range 5` at the boundary.
In Level 6, you confirmed that `Finset.range 0` is empty.

But the real power of `Finset.mem_range` is with **variables**.
The introduction to this world promised a bridge between `Fin n`
(Phase 1) and `Finset.range n` (Phase 2). Here it is.

Given a hypothesis `h : i < n`, prove that `i ∈ Finset.range n`.
The proof is the same pattern as Level 4:

1. `rw [Finset.mem_range]` — converts the goal to `i < n`
2. `exact h` — the hypothesis is exactly what we need

This is the **variable-n** version of the Phase 1 bound proof.
In Phase 1, you proved `3 < 5` to construct `⟨3, by omega⟩ : Fin 5`.
Here, you use the same bound `i < n` to prove membership in
`Finset.range n`. Same arithmetic, different packaging.
"

/-- An element below n belongs to Finset.range n. -/
Statement (n i : ℕ) (h : i < n) : i ∈ Finset.range n := by
  Hint "Use `rw [Finset.mem_range]` to convert the membership goal
  to an inequality."
  rw [Finset.mem_range]
  Hint "The goal is `i < n`, which is exactly `{h}`."
  exact h

Conclusion "
This is the bridge the introduction promised: `Finset.range n`
contains exactly the numbers that could be values of `Fin n`
elements. The proof move `rw [Finset.mem_range]; exact h` is the
finset analog of the `⟨i, h⟩ : Fin n` constructor.

| Phase 1 (Fin) | Phase 2 (Finset) |
|---|---|
| `⟨i, h⟩ : Fin n` | `i ∈ Finset.range n` |
| Requires `h : i < n` | Requires `h : i < n` |
| Typed index access | Set membership |

The bound proof `h : i < n` is the common currency between the
two interfaces. This connection becomes load-bearing later: when
you sum over `Finset.range n`, the bound proofs from `Fin n` will
transfer directly.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
