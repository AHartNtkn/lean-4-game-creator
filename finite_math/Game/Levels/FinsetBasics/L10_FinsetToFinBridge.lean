import Game.Metadata

World "FinsetBasics"
Level 10

Title "The Finset-to-Fin Bridge"

Introduction "
# The Converse: From Range Membership to Fin

Level 9 showed the forward direction: every `Fin n` element's value
belongs to `Finset.range n`. Now prove the **converse**: given
`k ∈ Finset.range n`, you can construct a `Fin n` element with
value `k`.

This completes the equivalence:

| Direction | Statement |
|---|---|
| Forward (L09) | `i : Fin n` implies `i.val ∈ Finset.range n` |
| Backward (this) | `k ∈ Finset.range n` implies there exists `i : Fin n` with `i.val = k` |

**Strategy**: Use `rw [Finset.mem_range] at hk` to extract
`hk : k < n`, then construct the `Fin n` element using the
anonymous constructor `⟨k, hk⟩`.
"

/-- Every element of Finset.range n corresponds to a Fin n element. -/
Statement (n : ℕ) (k : ℕ) (hk : k ∈ Finset.range n) :
    ∃ i : Fin n, i.val = k := by
  Hint "Convert `hk` from set membership to an inequality:
  `rw [Finset.mem_range] at hk`."
  rw [Finset.mem_range] at hk
  Hint "Now `hk : k < n`. Construct the `Fin n` element using
  the anonymous constructor: `use ⟨k, hk⟩`."
  Hint (hidden := true) "`use ⟨k, hk⟩` provides the witness.
  The goal `⟨k, hk⟩.val = k` is true by definition — `rfl`."
  use ⟨k, hk⟩

Conclusion "
This completes the **Fin-Finset bridge** in both directions:

- **Forward** (L09): `Fin n` → `Finset.range n` via `i.isLt`
- **Backward** (this): `Finset.range n` → `Fin n` via `⟨k, hk⟩`

The two types represent the **same mathematical object** through
different interfaces. `Fin n` gives ordered index access with
type-level length guarantees. `Finset.range n` gives unordered
set membership with decidable containment. The bridge lets you
move between them freely.

This equivalence will become important when you encounter
operations like `Finset.range n` in summations — the elements
being summed over are exactly the `Fin n` indices.

**Vocabulary preview**: The Fintype world generalizes this bridge.
`Fintype α` says 'the type `α` has finitely many elements,' and
`Finset.univ : Finset α` is the finset containing all of them.
For `Fin n`, `Finset.univ` has `n` elements — the same count as
`Finset.range n`, but typed as `Fin n` values rather than `ℕ` values.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
