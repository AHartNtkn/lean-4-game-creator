import Game.Metadata

World "SetOpsWorld"
Level 15

Title "Double Complement"

Introduction "
# sᶜᶜ = s

The complement of the complement returns you to the original set:

$$s^{cc} = s$$

This is set-theoretic **double negation elimination**: `x ∈ sᶜᶜ`
means `¬¬(x ∈ s)`, and in classical logic `¬¬P → P`.

**Proof plan**:
1. `ext x`, `constructor`
2. **Forward** (`x ∈ sᶜᶜ → x ∈ s`): This is the classical direction.
   You have `hx : ¬¬(x ∈ s)` and need `x ∈ s`. Use `by_contra h` to
   assume `x ∉ s`, then `exact hx h`.
3. **Backward** (`x ∈ s → x ∈ sᶜᶜ`): This is constructive. You have
   `hx : x ∈ s` and need `¬(x ∉ s)`, i.e., `(x ∈ s → False) → False`.
   Introduce the negation and apply it to `hx`.
"

/-- The complement of the complement is the original set. -/
Statement (α : Type) (s : Set α) : sᶜᶜ = s := by
  Hint "Use `ext x` to reduce to membership, then `constructor`."
  ext x
  constructor
  -- Forward: sᶜᶜ → s (classical — double negation elimination)
  · Hint "**Forward**: `hx : x ∈ sᶜᶜ` means `¬(x ∈ sᶜ)`, which is
    `¬¬(x ∈ s)`. You need `x ∈ s`. You cannot extract this directly —
    use `by_contra h` to assume `x ∉ s` and derive `False`."
    Hint (hidden := true) "`intro hx` then `by_contra h` then
    `exact hx h`."
    intro hx
    Hint "Use `by_contra h` — this gives `h : x ∉ s` (= `x ∈ sᶜ`)
    and changes the goal to `False`."
    by_contra h
    Hint "`hx : x ∈ sᶜᶜ` means `x ∈ sᶜ → False`, and `h : x ∉ s`
    means `h : x ∈ sᶜ`. Apply `hx` to `h`: `exact hx h`."
    exact hx h
  -- Backward: s → sᶜᶜ (constructive — double negation introduction)
  · Hint "**Backward**: `hx : x ∈ s` and the goal is `x ∈ sᶜᶜ`, which
    is `x ∈ sᶜ → False`, i.e., `(x ∉ s) → False`. Use `intro h` to
    assume `x ∉ s`, then derive `False` from `h` and `hx`."
    Hint (hidden := true) "`intro hx` then `intro h` then `exact h hx`."
    intro hx
    Hint "The goal is `x ∈ sᶜᶜ`, which is `¬(x ∈ sᶜ)`, which is
    `(x ∉ s) → False`. Use `intro h` to assume `x ∉ s`."
    intro h
    Hint "`h : x ∉ s` (i.e., `x ∈ s → False`) and `hx : x ∈ s`.
    Apply `h` to `hx`: `exact h hx`."
    exact h hx

Conclusion "
You proved `sᶜᶜ = s` — double complementation is the identity.

The forward direction is pure **double negation elimination**: from
`¬¬P`, conclude `P`. This required `by_contra` (classical logic),
just like the complement union law in the previous level.

The backward direction is **double negation introduction**: from `P`,
conclude `¬¬P`. This is constructive — no `by_contra` needed. Given
`x ∈ s` and assuming `x ∉ s`, we have a direct contradiction.

This identity tells us that complement is an **involution**: applying
it twice returns to the starting point. This is the set-theoretic
analogue of the logical fact `¬¬P ↔ P`.

The library name is `compl_compl`.
"

/-- `compl_compl` states `aᶜᶜ = a` — double complement is the identity. -/
TheoremDoc compl_compl as "compl_compl" in "Set"

NewTheorem compl_compl

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf compl_compl
