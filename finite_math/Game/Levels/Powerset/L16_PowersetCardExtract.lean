import Game.Metadata

World "Powerset"
Level 16

Title "Extracting from PowersetCard"

Introduction "
# Reading a PowersetCard Membership

In Level 15, you *built* a `mem_powersetCard` proof using
`constructor` to assemble the conjunction. Now go the other
direction: given that `t` is in `powersetCard k s`, extract
useful information.

When a hypothesis `ht` has type `A ∧ B` (a conjunction), you
can access the two components with **projection notation**:
- `ht.1` gives the left component (type `A`)
- `ht.2` gives the right component (type `B`)

**Your task**: Given `ht : t ∈ Finset.powersetCard 2 s`,
prove `t ∈ s.powerset`.

Strategy:
1. Rewrite `ht` with `mem_powersetCard` to get `t ⊆ s ∧ t.card = 2`
2. Rewrite the goal with `mem_powerset` to get `t ⊆ s`
3. Use `ht.1` to extract the subset component
"

/-- A member of powersetCard k s is also in the powerset of s. -/
Statement (s t : Finset ℕ) (ht : t ∈ Finset.powersetCard 2 s) :
    t ∈ s.powerset := by
  Hint "First, unwrap `ht` using `mem_powersetCard` to see the two
  conditions: `t ⊆ s` and `t.card = 2`."
  Hint (hidden := true) "Try `rw [Finset.mem_powersetCard] at ht`."
  rw [Finset.mem_powersetCard] at ht
  Hint "Now `ht : t ⊆ s ∧ t.card = 2`. The goal is `t ∈ s.powerset`.
  Rewrite the goal to a subset claim using `mem_powerset`."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset]`."
  rw [Finset.mem_powerset]
  Hint "The goal is `t ⊆ s`. You have `ht : t ⊆ s ∧ t.card = 2`.
  Use `ht.1` to extract the left component of the conjunction."
  Hint (hidden := true) "Try `exact ht.1`."
  exact ht.1

Conclusion "
Three steps:
1. `rw [mem_powersetCard] at ht` — unwrap to `t ⊆ s ∧ t.card = 2`
2. `rw [mem_powerset]` — convert goal to `t ⊆ s`
3. `exact ht.1` — extract the subset component

**Projection notation**: For `h : A ∧ B`:
- `h.1` is the left part (type `A`)
- `h.2` is the right part (type `B`)

This is the natural counterpart to `constructor`, which *builds*
a conjunction. Projection notation *deconstructs* one.

**Bridge level**: This connects `powersetCard` back to `powerset` —
every member of `powersetCard k s` is automatically in `s.powerset`.
The extra information (cardinality = k) is carried by `.2`.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
