import Game.Metadata

World "SubsetWorld"
Level 18

Title "Boss: Subset Chain"

Introduction "
# Boss: Chaining Subsets to Prove Equality

You have two sets `s` and `t` of natural numbers, with three
hypotheses:
- `hst : s ⊆ t` — `s` is contained in `t`
- `ht : t ⊆ {n | n ≤ 4}` — `t` is contained in the numbers at most 4
- `h5 : ∀ x, x < 5 → x ∈ s` — every number less than 5 is in `s`

Your task: prove `s = {n | n < 5}`.

Think about what this means. The hypothesis `h5` tells you that
`{n | n < 5} ⊆ s`. And from `hst` and `ht`, you can chain:
`s ⊆ t ⊆ {n | n ≤ 4}`. Since `n ≤ 4` is the same as `n < 5` for
natural numbers, this gives `s ⊆ {n | n < 5}`. Together with
`{n | n < 5} ⊆ s`, you get equality by antisymmetry.

This problem integrates the core skills of this world:
- **`ext` or `Set.Subset.antisymm`** to prove equality
- **`intro x hx`** to prove subsets
- **`change`/`show`** to unwrap set membership
- **Chaining subset hypotheses** (transitivity from Level 8)
- **`omega`** to bridge arithmetic facts

There are multiple valid strategies. Choose your own path!
"

/-- If s ⊆ t ⊆ {n | n ≤ 4} and every n < 5 is in s, then s = {n | n < 5}. -/
Statement (s t : Set ℕ)
    (hst : s ⊆ t)
    (ht : t ⊆ {n | n ≤ 4})
    (h5 : ∀ x, x < 5 → x ∈ s) :
    s = {n | n < 5} := by
  Hint "The goal is a set equality. Use `apply Set.Subset.antisymm`
  to split into two subset proofs, or `ext x` to reduce to a
  membership biconditional."
  Branch
    -- Ext path
    ext x
    Hint "Now `constructor` to split the `↔` into forward and backward."
    constructor
    · Hint "Forward: show that `x ∈ s` implies `x < 5`. You can
      chain: `hst` takes you from `s` to `t`, then `ht` takes you
      from `t` to the arithmetic set. Start with `intro hx`."
      intro hx
      Hint "Chain the subset hypotheses: apply `hst` to get `x ∈ t`,
      then `ht` to get membership in the arithmetic set.

      Try `have hxt := hst hx` then `have hle := ht hxt`."
      Hint (hidden := true) "Step by step:
      1. `have hxt := hst hx` — from `x ∈ s` to `x ∈ t`
      2. `have hle := ht hxt` — from `x ∈ t` to `x ∈ the arithmetic set`
      3. `change x ≤ 4 at hle` — unwrap the set membership
      4. `show x < 5` — unwrap the goal
      5. `omega` — derive `x < 5` from `x ≤ 4`"
      have hxt := hst hx
      have hle := ht hxt
      change x ≤ 4 at hle
      show x < 5
      omega
    · Hint "Backward: show that `x < 5` implies `x ∈ s`. The
      hypothesis `h5` gives this directly."
      intro hx
      Hint "Use `change x < 5 at hx` to unwrap, then `exact h5 x hx`."
      Hint (hidden := true) "`change x < 5 at hx` then `exact h5 x hx`."
      change x < 5 at hx
      exact h5 x hx
  apply Set.Subset.antisymm
  -- First direction: s ⊆ {n | n < 5}
  · Hint "First goal: `s ⊆ the right set`. You know `s ⊆ t` and
    `t ⊆ the arithmetic set`. Chain these subsets, then bridge the
    arithmetic. Start with `intro x hx`."
    intro x hx
    Hint "Now chain the subset hypotheses. Use `hst` to get `x ∈ t`,
    then `ht` to get the arithmetic membership.

    Try: `have hxt := hst hx` then `have hle := ht hxt`."
    Hint (hidden := true) "Step by step:
    1. `have hxt := hst hx` — from `x ∈ s` to `x ∈ t`
    2. `have hle := ht hxt` — from `x ∈ t` to `x ∈ the arithmetic set`
    3. `change x ≤ 4 at hle` — unwrap
    4. `show x < 5` — unwrap the goal
    5. `omega` — `x ≤ 4` implies `x < 5`"
    Branch
      -- One-step chaining
      have hle := ht (hst hx)
      Hint "Now `hle` says `x` is in the arithmetic set. Unwrap with
      `change x ≤ 4 at hle`, then `show x < 5` and `omega`."
      change x ≤ 4 at hle
      show x < 5
      omega
    Branch
      -- Using Set.Subset.trans
      have h_chain := Set.Subset.trans hst ht
      Hint "`h_chain : s ⊆ the arithmetic set`. Apply it to `hx`:
      `have hle := h_chain hx`."
      have hle := h_chain hx
      change x ≤ 4 at hle
      show x < 5
      omega
    have hxt := hst hx
    Hint "`hxt : x ∈ t`. Now apply `ht`: `have hle := ht hxt`."
    have hle := ht hxt
    Hint "`hle` says `x` is in the arithmetic set, which is
    definitionally `x ≤ 4`. Unwrap with `change x ≤ 4 at hle`,
    then `show x < 5` and `omega`."
    change x ≤ 4 at hle
    show x < 5
    omega
  -- Second direction: {n | n < 5} ⊆ s
  · Hint "Second goal: the arithmetic set ⊆ `s`. The hypothesis
    `h5 : ∀ x, x < 5 → x ∈ s` gives this. Start with `intro x hx`."
    intro x hx
    Hint "`hx` is `x ∈ the arithmetic set`, i.e., `x < 5`.
    Unwrap with `change x < 5 at hx`, then `exact h5 x hx`."
    Hint (hidden := true) "`change x < 5 at hx` then `exact h5 x hx`."
    change x < 5 at hx
    exact h5 x hx

Conclusion "
Congratulations — you have completed **Subset World**!

Here is your toolkit:

| Concept | Lean | Proof move |
|---|---|---|
| Subset `s ⊆ t` | `∀ x, x ∈ s → x ∈ t` | `intro x hx` then show `x ∈ t` |
| Reflexivity `s ⊆ s` | identity | `intro x hx; exact hx` |
| `∅ ⊆ s` | vacuously true | `intro x hx; contradiction` |
| `s ⊆ Set.univ` | trivially true | `intro x _; constructor` |
| Transitivity | `s ⊆ t → t ⊆ u → s ⊆ u` | chain with `Set.Subset.trans` or function application |
| Set equality via ext | `s = t ↔ ∀ x, x ∈ s ↔ x ∈ t` | `ext x; constructor; ...` |
| Set equality via antisymm | `s ⊆ t → t ⊆ s → s = t` | `exact Set.Subset.antisymm h1 h2` |
| Set non-equality `s ≠ t` | `(s = t) → False` | assume equality, find contradictory witness |
| Proper subset `s ⊂ t` | `s ⊆ t ∧ ¬ (t ⊆ s)` | `constructor`, then prove ⊆ and ¬⊆ |
| Unwrap hypothesis | `change P at h` | converts display to def-equal form |
| Dot projection | `h.1`, `h.2` | extract components of `∧` or `↔` |

The `⊆` relation is a **partial order** on sets: it is reflexive
(Level 3), transitive (Level 8), and antisymmetric (Level 14). The
strict variant `⊂` (proper subset, Level 15) excludes equality.

In the next world, you will learn about **set operations**: union (`∪`),
intersection (`∩`), complement (`ᶜ`), and difference (`\\`). Each
operation corresponds to a logical connective, extending the
sets-as-predicates theme from Set World. The `intro x hx` proof
pattern you mastered here will be the foundation for every one of
those proofs.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
