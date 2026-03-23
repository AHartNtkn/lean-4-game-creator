import Game.Metadata

World "SubsetWorld"
Level 5

Title "Every Set is in Set.univ"

Introduction "
# The Universal Superset: s ⊆ Set.univ

The mirror image of Level 3: every set is a subset of `Set.univ`.

$$s \\subseteq \\texttt{Set.univ} \\quad \\text{for any } s$$

Why? Because `x ∈ Set.univ` is always `True`, so the obligation
`x ∈ s → x ∈ Set.univ` reduces to `x ∈ s → True` — and `True`
needs no proof beyond `constructor`.

After `intro x hx`, the goal is `x ∈ Set.univ`, which reduces to
`True`. You can ignore `hx` entirely.

**Proof plan**:
1. `intro x hx` — introduce element and membership hypothesis
2. `constructor` — prove `True` (which is what `x ∈ Set.univ` reduces to)
"

/-- Any set is a subset of the universal set. -/
Statement (α : Type) (s : Set α) : s ⊆ Set.univ := by
  Hint "As with any `⊆` proof, start with `intro x hx`."
  intro x hx
  Hint "The goal is `x ∈ Set.univ`, which is `True`. The hypothesis
  `hx` is not needed here — `True` holds unconditionally. Use
  `constructor`."
  constructor

Conclusion "
Two boundary facts about subsets are now established:

| Statement | Intuition | Proof key |
|---|---|---|
| `∅ ⊆ s` | Nothing is in `∅`, so the claim is vacuously true | `contradiction` |
| `s ⊆ Set.univ` | Everything is in `Set.univ`, so the obligation is trivial | `constructor` |

These are the extreme cases: `∅` is the smallest set (contained in
everything) and `Set.univ` is the largest (contains everything).
For any set `s`:
$$\\emptyset \\subseteq s \\subseteq \\texttt{Set.univ}$$

The library names are `Set.empty_subset` and `Set.subset_univ`.
"

/-- `Set.subset_univ s` proves `s ⊆ Set.univ` for any set `s`. -/
TheoremDoc Set.subset_univ as "Set.subset_univ" in "Set"

NewTheorem Set.subset_univ

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.subset_univ Set.mem_setOf_eq Set.mem_setOf le_top OrderTop.le_top
