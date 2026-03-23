import Game.Metadata

World "SubsetWorld"
Level 16

Title "Deriving Extensionality from Antisymmetry"

Introduction "
# The Other Direction

In Level 15, you derived antisymmetry from extensionality: given two
subset proofs, you used `ext` to prove equality without
`Set.Subset.antisymm`.

Now prove the reverse direction: given a pointwise membership
equivalence `h : ∀ x, x ∈ s ↔ x ∈ t`, prove `s = t` using
`Set.Subset.antisymm` alone — without `ext` (which is disabled).

The key insight: an `↔` contains two implications. If `hiff : P ↔ Q`,
then `hiff.1` is the forward direction `P → Q` and `hiff.2` is the
backward direction `Q → P`. So `(h x).1` gives `x ∈ s → x ∈ t` and
`(h x).2` gives `x ∈ t → x ∈ s` — exactly the membership implications
you need for two subset proofs.

**Proof plan**:
1. `apply Set.Subset.antisymm` — reduce to two subset goals
2. **First subset** (`s ⊆ t`): `intro x hx; exact (h x).1 hx`
3. **Second subset** (`t ⊆ s`): `intro x hx; exact (h x).2 hx`
"

/-- Set equality from pointwise membership equivalence, without ext. -/
Statement (α : Type) (s t : Set α) (h : ∀ x, x ∈ s ↔ x ∈ t) :
    s = t := by
  Hint "You need to prove `s = t` without `ext` (which is disabled).
  Use `apply Set.Subset.antisymm` to split into two subset goals."
  apply Set.Subset.antisymm
  · Hint "Goal: `s ⊆ t`. Use `intro x hx` as always for a subset proof."
    intro x hx
    Hint "`hx : x ∈ s`. The hypothesis `h x` gives an `↔` between
    `x ∈ s` and `x ∈ t`. Use `.1` to extract the forward direction:
    `(h x).1` is the implication `x ∈ s → x ∈ t`. Apply it to `hx`
    with `exact (h x).1 hx`."
    Hint (hidden := true) "`exact (h x).1 hx` — `(h x).1` is the
    forward implication of the biconditional, and `hx` provides `x ∈ s`."
    exact (h x).1 hx
  · Hint "Goal: `t ⊆ s`. Same pattern, but use `.2` for the backward
    direction."
    intro x hx
    Hint "Use `(h x).2` for the backward direction: `exact (h x).2 hx`."
    Hint (hidden := true) "`exact (h x).2 hx` — `(h x).2` is the
    backward implication of the biconditional."
    exact (h x).2 hx

Conclusion "
You have now proved both directions of the equivalence:

| Level | Proved | Strategy |
|---|---|---|
| Level 15 | antisymm from ext | `ext` decomposes `=` into `↔`, matching two ⊆ proofs |
| This level | ext from antisymm | `↔` decomposes into two ⊆ proofs, matching antisymm |

**Decomposing `↔`**: The `.1` and `.2` projections on an `↔` extract
the two directions. If `hiff : P ↔ Q`, then:
- `hiff.1 : P → Q` (forward, also called `Iff.mp`)
- `hiff.2 : Q → P` (backward, also called `Iff.mpr`)

This equivalence confirms that `ext` and `antisymm` are two faces of
the same principle. Stated as a single theorem:

**For sets `s` and `t`, `s = t` if and only if `s ⊆ t ∧ t ⊆ s`.**

The axiom of extensionality and the antisymmetry of `⊆` are logically
interchangeable — use whichever is more convenient for the problem
at hand.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith ext
DisabledTheorem Set.ext_iff Set.mem_setOf_eq Set.mem_setOf
