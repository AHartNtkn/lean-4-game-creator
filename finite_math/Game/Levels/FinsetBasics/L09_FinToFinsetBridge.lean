import Game.Metadata

World "FinsetBasics"
Level 9

Title "The Fin-to-Finset Bridge"

Introduction "
# Connecting Fin to Finset.range

In Phase 1, every element `i : Fin n` carried a proof `i.isLt : i.val < n`.
In Levels 7-8, you proved that `i ∈ Finset.range n ↔ i < n`.

These are the same condition! Every `Fin n` element's value is automatically
in `Finset.range n`. This is the concrete bridge between Phase 1 (indexed
access) and Phase 2 (set membership).

**Your task**: Prove that for any `i : Fin n`, the value `i.val` belongs
to `Finset.range n`.

**Strategy**: Use `rw [Finset.mem_range]` to convert to `i.val < n`,
then use `exact i.isLt` — the bound proof that every `Fin n` element
carries.
"

/-- Every Fin n element's value belongs to Finset.range n. -/
Statement (n : ℕ) (i : Fin n) : i.val ∈ Finset.range n := by
  Hint "Convert the membership goal to an inequality:
  `rw [Finset.mem_range]`."
  rw [Finset.mem_range]
  Hint "The goal is `i.val < n`. Every element of `Fin n` carries
  exactly this proof — it's called `i.isLt`. Use `exact i.isLt`."
  exact i.isLt

Conclusion "
This level makes the Phase 1 → Phase 2 connection concrete:

| Phase 1 (Fin n) | Phase 2 (Finset.range n) |
|---|---|
| `i : Fin n` | `i.val ∈ Finset.range n` |
| `i.isLt : i.val < n` | `mem_range` converts to `i.val < n` |
| Ordered index access | Unordered set membership |

The bound proof `i.isLt` is the bridge: it's the proof that `Fin n`
carries internally, and it's exactly what `Finset.mem_range` requires.

This is the forward direction of the bridge. In the next level,
you'll prove the **converse**: given `k ∈ Finset.range n`, you
can construct a `Fin n` element with value `k`. Together, these
two levels establish a complete equivalence between `Fin n` and
`Finset.range n`.

When you encounter `Finset.range n` in later worlds — especially in
summation (`∑ i ∈ Finset.range n, f i`) — remember that its elements
are exactly the values that `Fin n` indices can take.

**Looking ahead**: In the Fintype world, you'll learn about
`Finset.univ : Finset (Fin n)` — the finset of ALL elements of a
finite type. While `Finset.range n` contains the *natural number values*
`0, 1, ..., n-1`, `Finset.univ` contains the *Fin n elements* themselves.
The cardinality is the same: `Fintype.card (Fin n) = n`.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
