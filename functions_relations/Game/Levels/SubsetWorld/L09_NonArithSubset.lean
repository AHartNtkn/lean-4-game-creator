import Game.Metadata

World "SubsetWorld"
Level 9

Title "Beyond Arithmetic"

Introduction "
# Subsets Are About Predicates, Not Just Arithmetic

Every subset proof so far ended with `omega` — because every set was
defined by an arithmetic inequality like `n < 3` or `n ≤ 5`.

But `⊆` is not about arithmetic. It is about **predicates**: `s ⊆ t`
means that the predicate defining `s` implies the predicate defining `t`.
The closing move depends entirely on what those predicates are.

In this level, the sets are defined by abstract predicates `p` and `q`
on a general type `α` (not necessarily `ℕ`). You are given
`h : ∀ x, p x → q x` — a pointwise implication between the
predicates. Your task is to prove the subset inclusion.

The proof follows the same `intro x hx` pattern. But the closing move
is not `omega` — it is `exact h x hx`, applying the given implication.

**Proof plan**:
1. `intro x hx` — assume `x` is in the left set (i.e., `p x` holds)
2. `exact h x hx` — apply the implication to get `q x`
"

/-- If p implies q pointwise, then the set defined by p is a subset of the set defined by q. -/
Statement (α : Type) (p q : α → Prop) (h : ∀ x, p x → q x) :
    {x : α | p x} ⊆ {x | q x} := by
  Hint "Start with `intro x hx` as always for a `⊆` proof."
  intro x hx
  Hint "Now `hx` says `x` is in the left set, which is definitionally
  `p x`. The goal says `x` is in the right set, which is definitionally
  `q x`. The hypothesis `h` says `∀ x, p x → q x` — applied to `x`
  and `hx`, it gives exactly `q x`. Use `exact h x hx`."
  Hint (hidden := true) "`exact h x hx` — `h x` specializes the
  implication to our element, and `hx` provides the premise `p x`.
  So `h x hx` is a proof of `q x`, which matches the goal."
  Branch
    apply h
    exact hx
  exact h x hx

Conclusion "
No `omega`! The closing move was `exact h x hx` — applying a hypothesis.

This level demonstrates the key insight: **subset proofs are about
predicates**. The `intro x hx` pattern is universal, but the closing
move depends on the relationship between the predicates:

| Predicate type | Closing move |
|---|---|
| Arithmetic (`n < 3`, `n ≤ 5`) | `omega` |
| Implication from hypothesis | `exact h x hx` or `apply h; exact hx` |
| Vacuously true (`x ∈ ∅`) | `contradiction` |
| Trivially true (`x ∈ Set.univ`) | `constructor` |

The proof pattern is always the same:
1. `intro x hx` — enter the subset proof
2. (optional) unwrap with `change`/`show`
3. Close with whatever fits the specific predicates

This table will keep growing as you encounter more types of predicates
throughout the course.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
