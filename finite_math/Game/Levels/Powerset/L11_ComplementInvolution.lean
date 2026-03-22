import Game.Metadata

World "Powerset"
Level 11

Title "The Complement Is Its Own Inverse"

Introduction "
# Complement Involution

The complement map sends `t` to `s \\ t`. What happens if you
complement *again*? You get back to `t`:

$$s \\setminus (s \\setminus t) = t \\quad \\text{when } t \\subseteq s$$

This means the complement map is an **involution** — applying it
twice returns you to where you started. An involution is automatically
a bijection (it is its own inverse), so the complement map gives a
one-to-one correspondence between `k`-element and `(n-k)`-element
subsets of `s`.

Combined with Level 10 (complement cardinality), this completes the
bijective proof of $\\binom{n}{k} = \\binom{n}{n-k}$:
1. The complement maps subsets to subsets (Level 9)
2. It sends `k`-element subsets to `(n-k)`-element subsets (Level 10)
3. It is its own inverse, hence a bijection (this level)

**Your task**: Given `ht : t ∈ s.powerset`, prove `s \\ (s \\ t) = t`.

The Mathlib lemma `sdiff_sdiff_eq_self` proves exactly this for any
structure where set difference is well-behaved (including `Finset`).
"

/-- The double complement of a subset of s returns the original set. -/
Statement (s t : Finset ℕ) (ht : t ∈ s.powerset) : s \ (s \ t) = t := by
  Hint "First, extract `t ⊆ s` from powerset membership."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : t ⊆ s`. The goal is `s \\ (s \\ t) = t`. The Mathlib
  lemma `sdiff_sdiff_eq_self` states that `x \\ (x \\ y) = y` when
  `y ≤ x` (i.e., `y ⊆ x` for finsets). Apply it with `ht`."
  Hint (hidden := true) "Try `exact sdiff_sdiff_eq_self ht`."
  exact sdiff_sdiff_eq_self ht

Conclusion "
Two steps: `rw [mem_powerset] at ht` then `exact sdiff_sdiff_eq_self ht`.

**The complement bijection is now complete**:
- Level 9: `t ∈ s.powerset → s \\ t ∈ s.powerset` (closure)
- Level 10: `(s \\ t).card = s.card - t.card` (size)
- This level: `s \\ (s \\ t) = t` (involution)

The complement map is an involution on the powerset that swaps
`k`-element subsets with `(n-k)`-element subsets. Since it is its
own inverse, it is a bijection, which means the two sets have the
same cardinality: $\\binom{n}{k} = \\binom{n}{n-k}$.

**Note on the Lean proof**: `sdiff_sdiff_eq_self` works at the
*lattice* level — it holds in any generalized Boolean algebra, not
just for finsets. Finsets form such an algebra, so the general lemma
applies. You will sometimes see lattice-level lemmas (without the
`Finset.` prefix) being used for finset goals; this is because
Lean's typeclass system automatically applies the right algebraic
structure.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono Finset.sdiff_sdiff_self_left sdiff_sdiff_right_self Finset.sdiff_sdiff_eq_self Finset.inter_eq_right inf_eq_right
