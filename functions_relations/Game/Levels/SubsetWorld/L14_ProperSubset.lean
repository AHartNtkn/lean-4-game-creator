import Game.Metadata

World "SubsetWorld"
Level 14

Title "Proper Subsets"

Introduction "
# Strict Containment: The Proper Subset ⊂

You have proved all three partial order axioms for `⊆` (reflexivity,
transitivity, antisymmetry). Antisymmetry says: if `s ⊆ t` and
`t ⊆ s`, then `s = t`. In other words, mutual containment forces
equality.

But what about **strict** containment — when one set is inside
another but they are NOT equal? This is the **proper subset**
relation, written `s ⊂ t`.

In Lean, `s ⊂ t` means `s ⊆ t ∧ ¬ (t ⊆ s)` — `s` is contained in
`t`, and the containment is strict (there is something in `t` that is
not in `s`).

To prove `s ⊂ t`, use `constructor` to split into two goals:
1. Prove `s ⊆ t` — a familiar subset proof
2. Prove `¬ (t ⊆ s)` — a familiar non-subset proof (Level 7)

This level integrates two skills you have already mastered!

**Proof plan**:
1. `constructor` — split `⊂` into `⊆` and `¬ ⊆`
2. **First goal** (`⊆`): prove the subset as in Level 1
3. **Second goal** (`¬ ⊆`): disprove the reverse as in Level 7
"

/-- The set of numbers less than 3 is a proper subset of the set
of numbers less than 5. -/
Statement : {n : ℕ | n < 3} ⊂ {n : ℕ | n < 5} := by
  Hint "The goal is `s ⊂ t`, which means `s ⊆ t ∧ ¬ (t ⊆ s)`.
  Use `constructor` to split it into the two components."
  constructor
  -- First component: {n | n < 3} ⊆ {n | n < 5}
  · Hint "First goal: prove the subset inclusion. This is the same
    as Level 1! Use `intro x hx`, unwrap, and close."
    Hint (hidden := true) "`intro x hx` then `show x < 5` then
    `change x < 3 at hx` then `omega`."
    intro x hx
    Hint "Unwrap the set membership and use arithmetic."
    show x < 5
    change x < 3 at hx
    omega
  -- Second component: ¬ ({n | n < 5} ⊆ {n | n < 3})
  · Hint "Second goal: prove the reverse inclusion is false. This is
    the same technique as Level 7 — assume the reverse subset holds,
    exhibit a counterexample, and derive contradiction.

    Use `intro h` to assume the reverse subset."
    intro h
    Hint "Now `h` says every number less than 5 is less than 3. Use
    the counterexample `4`: prove `4 < 5` then apply `h`.

    `have h4 : (4 : ℕ) < 5 := by omega`"
    Hint (hidden := true) "Step by step:
    1. `have h4 : (4 : ℕ) < 5 := by omega`
    2. `have h4' := h h4`
    3. `change (4 : ℕ) < 3 at h4'`
    4. `omega`"
    have h4 : (4 : ℕ) < 5 := by omega
    Hint "Apply the assumed reverse inclusion to the witness:
    `have h4' := h h4`."
    have h4' := h h4
    Hint "`h4'` says `4` is in the left set, i.e., `4 < 3`. Unwrap
    and derive contradiction."
    change (4 : ℕ) < 3 at h4'
    omega

Conclusion "
You proved your first **proper subset**! The structure was:

1. `constructor` — split `⊂` into `⊆` and `¬ (reverse ⊆)`
2. Prove the subset (Level 1 technique)
3. Disprove the reverse (Level 7 technique)

This is a satisfying integration: proper subset combines two skills
you already know. The concept connects directly to antisymmetry —
antisymmetry says mutual `⊆` implies `=`, so proper subset is
exactly the case where equality is ruled out because the reverse
containment fails.

| Relation | Meaning | Lean |
|---|---|---|
| `s ⊆ t` | `s` is contained in `t` (possibly equal) | `∀ x, x ∈ s → x ∈ t` |
| `s ⊂ t` | `s` is strictly contained in `t` | `s ⊆ t ∧ ¬ (t ⊆ s)` |
| `s = t` | `s` and `t` have the same elements | `∀ x, x ∈ s ↔ x ∈ t` |
| `s ≠ t` | `s` and `t` differ on some element | `(s = t) → False` |

**Alternative characterization**: You may know proper subset as
`s ⊆ t ∧ s ≠ t` rather than Lean's `s ⊆ t ∧ ¬(t ⊆ s)`. These are
equivalent — by antisymmetry (Level 13), `s ⊆ t ∧ t ⊆ s → s = t`,
so `s ≠ t → ¬(t ⊆ s)` when `s ⊆ t` is known, and conversely. Both
definitions capture the same idea: strict containment with no equality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.not_subset
