import Game.Metadata

/-! ## Shared TheoremDoc and DefinitionDoc for IndexedOpsWorld

These documentation entries are used by `NewTheorem` / `NewDefinition`
in multiple level files. Keeping them here avoids "Missing Documentation"
build warnings.
-/

-- ===== Theorem documentation (shared) =====

/-- `Set.mem_iUnion` states `x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i` —
membership in an indexed union is equivalent to existence of a
witness index.

## Syntax
```
rw [Set.mem_iUnion]       -- in the goal
rw [Set.mem_iUnion] at h  -- in a hypothesis
```

## When to use it
When you see `⋃ i, s i` in a goal or hypothesis and need to
work with the underlying `∃` statement.

## Example
```
-- Goal: x ∈ ⋃ i, s i
rw [Set.mem_iUnion]
-- Goal: ∃ i, x ∈ s i
use j
-- Goal: x ∈ s j
```

## Warning
After `rw [Set.mem_iUnion]`, you get an `∃` — use `use` to provide
the witness. Do not confuse with `left`/`right` (which are for binary
`∨` / `∪`).
-/
TheoremDoc Set.mem_iUnion as "Set.mem_iUnion" in "Set"

/-- `Set.mem_iInter` states `x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i` —
membership in an indexed intersection is equivalent to membership
in every set of the family.

## Syntax
```
rw [Set.mem_iInter]       -- in the goal
rw [Set.mem_iInter] at h  -- in a hypothesis
```

## When to use it
When you see `⋂ i, s i` in a goal or hypothesis and need to
work with the underlying `∀` statement.

## Example
```
-- Goal: x ∈ ⋂ i, s i
rw [Set.mem_iInter]
-- Goal: ∀ i, x ∈ s i
intro i
-- Goal: x ∈ s i
```

## Warning
After `rw [Set.mem_iInter]`, you get a `∀` — use `intro` to
introduce the index variable. Do not confuse with `constructor`
(which is for binary `∧` / `∩`).
-/
TheoremDoc Set.mem_iInter as "Set.mem_iInter" in "Set"

/-- `Set.mem_iUnion₂` states
`x ∈ ⋃ (i) (j), s i j ↔ ∃ i j, x ∈ s i j` — membership in a
doubly-indexed union (including bounded indexed unions `⋃ i ∈ t`)
is equivalent to a double existential.

## Syntax
```
rw [Set.mem_iUnion₂]       -- in the goal
rw [Set.mem_iUnion₂] at h  -- in a hypothesis
```

## When to use it
When you see `⋃ i ∈ t, s i` (bounded indexed union) and need to
work with the underlying `∃ i, ∃ (_ : i ∈ t), x ∈ s i`.

## Example
```
-- Goal: x ∈ ⋃ i ∈ t, s i
rw [Set.mem_iUnion₂]
-- Goal: ∃ i, ∃ (_ : i ∈ t), x ∈ s i
use j       -- provide the index
use hj      -- provide proof that j ∈ t
-- Goal: x ∈ s j
```

## Comparison with `Set.mem_iUnion`
- `Set.mem_iUnion`: one `∃`, one `use`
- `Set.mem_iUnion₂`: two nested `∃`, two `use` steps
-/
TheoremDoc Set.mem_iUnion₂ as "Set.mem_iUnion₂" in "Set"

/-- `Set.mem_iInter₂` states
`x ∈ ⋂ (i) (j), s i j ↔ ∀ i j, x ∈ s i j` — membership in a
doubly-indexed intersection (including bounded indexed intersections
`⋂ i ∈ t`) is equivalent to a double universal.

## Syntax
```
rw [Set.mem_iInter₂]       -- in the goal
rw [Set.mem_iInter₂] at h  -- in a hypothesis
```

## When to use it
When you see `⋂ i ∈ t, s i` (bounded indexed intersection) and need to
work with the underlying `∀ i, i ∈ t → x ∈ s i`.

## Example
```
-- hx : x ∈ ⋂ i ∈ t, s i
rw [Set.mem_iInter₂] at hx
-- hx : ∀ i, i ∈ t → x ∈ s i
exact hx j hj
-- closes goal x ∈ s j (given hj : j ∈ t)
```

## Comparison with `Set.mem_iInter`
- `Set.mem_iInter`: `∀ i, ...` — one specialize step
- `Set.mem_iInter₂`: `∀ i, i ∈ t → ...` — two steps (index + guard)
-/
TheoremDoc Set.mem_iInter₂ as "Set.mem_iInter₂" in "Set"

/-- `Set.mem_prod` states `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t` —
membership in a cartesian product is equivalent to a conjunction of
memberships.

## Syntax
```
rw [Set.mem_prod]       -- in the goal
rw [Set.mem_prod] at h  -- in a hypothesis
```

## When to use it
When you see `×ˢ` in a goal or hypothesis and need to work with
the underlying `∧` (conjunction).

## Example
```
-- Goal: (a, b) ∈ s ×ˢ t
rw [Set.mem_prod]
-- Goal: a ∈ s ∧ b ∈ t
constructor
· ...  -- prove a ∈ s
· ...  -- prove b ∈ t
```
-/
TheoremDoc Set.mem_prod as "Set.mem_prod" in "Set"

/-- `Set.mem_powerset_iff` states `t ∈ 𝒫 s ↔ t ⊆ s` — membership
in the powerset is equivalent to being a subset.

## Syntax
```
rw [Set.mem_powerset_iff]       -- in the goal
rw [Set.mem_powerset_iff] at h  -- in a hypothesis
```

## When to use it
When you see `𝒫` and need to reduce powerset membership to
a subset relation.

## Example
```
-- Goal: t ∈ 𝒫 s
rw [Set.mem_powerset_iff]
-- Goal: t ⊆ s
intro x hx
...
```
-/
TheoremDoc Set.mem_powerset_iff as "Set.mem_powerset_iff" in "Set"

-- ===== Definition documentation (shared) =====

/-- The indexed union `⋃ i, s i` is the set of all elements that
belong to at least one `s i`. It generalizes binary union to
arbitrary families of sets. -/
DefinitionDoc Set.iUnion as "Set.iUnion"

/-- The indexed intersection `⋂ i, s i` is the set of all elements
that belong to every `s i`. It generalizes binary intersection to
arbitrary families of sets. -/
DefinitionDoc Set.iInter as "Set.iInter"

/-- The cartesian product `s ×ˢ t` is the set of all pairs `(a, b)`
with `a ∈ s` and `b ∈ t`. -/
DefinitionDoc Set.prod as "Set.prod"

/-- `Set.Nonempty s` means `∃ x, x ∈ s` — the set has at least one
element.

## When to use it
When a goal asks you to show a set is nonempty. Use `use` to
provide the witness element, then prove it belongs to the set.

## Example
```
-- Goal: Set.Nonempty {n | n > 5}
use 6
-- Goal: 6 ∈ {n | n > 5}
show 6 > 5
omega
```
-/
DefinitionDoc Set.Nonempty as "Set.Nonempty"

/-- The powerset `𝒫 s` is the set of all subsets of `s`. -/
DefinitionDoc Set.powerset as "Set.powerset"

/-- `Empty` is a type with no elements — no constructors at all.
It is the type-level analogue of `False` (which is a proposition
with no proofs).

If you have `i : Empty`, then `i.elim` (equivalently, `Empty.elim i`)
can prove any goal — because such an `i` cannot exist. This is the
principle of explosion for types, just as `False.elim` is the
principle of explosion for propositions.
-/
DefinitionDoc Empty as "Empty"
