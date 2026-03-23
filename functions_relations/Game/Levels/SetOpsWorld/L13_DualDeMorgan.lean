import Game.Metadata

World "SetOpsWorld"
Level 13

Title "Dual De Morgan"

Introduction "
# Dual De Morgan: (s ∩ t)ᶜ = sᶜ ∪ tᶜ

In Level 12, you proved $(s \\cup t)^c = s^c \\cap t^c$. Now prove the
**dual**: the complement of an intersection is the union of the
complements:

$$(s \\cap t)^c = s^c \\cup t^c$$

The proof has a **genuinely different structure** from the union version.
The forward direction requires a new technique: **proof by contradiction**.

**New tactic: `by_contra`**

When you cannot build the goal directly, assume its negation and derive
a contradiction:

```
by_contra h
-- h : ¬(goal)
-- new goal: False
```

**Why is this needed here?** The forward direction gives you
`hx : ¬(x ∈ s ∧ x ∈ t)` and asks for `x ∉ s ∨ x ∉ t`. You cannot
directly choose `left` or `right` without knowing which of `x ∈ s` or
`x ∈ t` fails. But if you assume the goal is FALSE (`by_contra h`),
then `push_neg at h` converts `¬(x ∉ s ∨ x ∉ t)` to `x ∈ s ∧ x ∈ t`
— which contradicts `hx`.

**Proof plan**:
1. `ext x`, `constructor`
2. **Forward**: `intro hx`, `by_contra h`, `change` + `push_neg at h`, `exact hx h`
3. **Backward**: `intro hx`, `intro hst`, destructure and case-split
"

/-- Dual De Morgan: the complement of an intersection is the union
of the complements. -/
Statement (α : Type) (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: (s ∩ t)ᶜ → sᶜ ∪ tᶜ
  · Hint "**Forward direction**: You have `hx : x ∈ (s ∩ t)ᶜ`, meaning
    `¬(x ∈ s ∧ x ∈ t)`. You need `x ∈ sᶜ ∪ tᶜ`, meaning `x ∉ s ∨ x ∉ t`.

    You cannot choose `left` or `right` directly — you do not know which
    of `x ∈ s` or `x ∈ t` fails. Use `by_contra h` to assume the goal
    is false, then use `push_neg` to derive a contradiction."
    intro hx
    Hint "Use `by_contra h` — this assumes `h : ¬(x ∈ sᶜ ∪ tᶜ)` and
    changes the goal to `False`."
    Hint (hidden := true) "`by_contra h` then
    `change ¬(x ∉ s ∨ x ∉ t) at h` then `push_neg at h` then
    `exact hx h`."
    by_contra h
    Hint "`h : ¬(x ∈ sᶜ ∪ tᶜ)` says neither `x ∉ s` nor `x ∉ t` holds.
    Use `change ¬(x ∉ s ∨ x ∉ t) at h` to make the logical structure
    visible, then `push_neg at h` to convert to `x ∈ s ∧ x ∈ t`."
    change ¬(x ∉ s ∨ x ∉ t) at h
    push_neg at h
    Hint "`h : x ∈ s ∧ x ∈ t`. But `hx` says `¬(x ∈ s ∧ x ∈ t)`.
    These contradict: `exact hx h`."
    exact hx h
  -- Backward: sᶜ ∪ tᶜ → (s ∩ t)ᶜ
  · Hint "**Backward direction**: Given `hx : x ∈ sᶜ ∪ tᶜ`, prove
    `x ∈ (s ∩ t)ᶜ`, which means `x ∈ s ∩ t → False`.

    Use `intro hx` then `intro hst` to assume `x ∈ s ∩ t`,
    destructure, and case-split on the union."
    intro hx
    Hint "The goal is `x ∈ (s ∩ t)ᶜ`, which is `¬(x ∈ s ∩ t)`.
    Use `intro hst` to assume `x ∈ s ∩ t`."
    intro hst
    Hint "Destructure `hst : x ∈ s ∩ t` with `obtain ⟨hs, ht⟩ := hst`,
    then case-split on `hx` to find the contradiction."
    Hint (hidden := true) "`obtain ⟨hs, ht⟩ := hst` then
    `cases hx with | inl hns | inr hnt`.
    In each case, apply the complement to the membership."
    obtain ⟨hs, ht⟩ := hst
    Hint "Now `hs : x ∈ s`, `ht : x ∈ t`, and `hx : x ∈ sᶜ ∪ tᶜ`.
    Case-split on `hx`: `cases hx with | inl hns | inr hnt`."
    cases hx with
    | inl hns =>
      Hint "`hns : x ∈ sᶜ` (= `x ∉ s`) and `hs : x ∈ s`. Contradiction:
      `exact hns hs`."
      Branch
        contradiction
      exact hns hs
    | inr hnt =>
      Hint "`hnt : x ∈ tᶜ` (= `x ∉ t`) and `ht : x ∈ t`. Contradiction:
      `exact hnt ht`."
      Branch
        contradiction
      exact hnt ht

Conclusion "
You proved the dual De Morgan law! Notice how the proof structure
differs from Level 12:

| | Union De Morgan | Intersection De Morgan |
|---|---|---|
| **Forward** | `change` + `push_neg` (direct) | `by_contra` + `push_neg` (indirect) |
| **Backward** | `intro` + `cases` on union | `intro` + `obtain` + `cases` on union |

The forward direction required **proof by contradiction** (`by_contra`)
because the goal was a disjunction where neither side could be chosen
without more information. This is a fundamental technique:

> When you cannot build the goal directly, assume its negation and
> derive a contradiction.

The `by_contra` + `push_neg` combination is especially powerful: it
converts a goal you cannot prove constructively into hypotheses you
can use to find a contradiction.

**The pattern**: Conjunction/intersection results tend to be
constructive (you can build `P ∧ Q` by producing each piece), while
disjunction/union results tend to require classical reasoning (you
must *choose* a side, and sometimes you cannot know which is true
without indirect argument). Watch for this asymmetry in future proofs:
if your goal is a disjunction and you cannot pick a side, `by_contra`
is likely the way forward.

**What is classical reasoning?** Classical logic means we accept that
every proposition is either true or false — there is no middle ground.
Not all proof systems accept this (constructive logic does not), but
Lean does, so `by_contra` is always available. The philosophical
difference: in constructive logic, to prove `P ∨ Q` you must *exhibit*
which one holds. In classical logic, you can prove `P ∨ Q` by showing
that assuming neither leads to contradiction.

The library name is `Set.compl_inter`.
"

/-- `by_contra` proves the goal by contradiction. It introduces the
negation of the goal as a hypothesis, and changes the goal to `False`.

## Syntax
```
by_contra h
```

## When to use it
When you cannot build the goal directly. After `by_contra h`, you have
`h : ¬(goal)` in context and must derive `False`.

## Example
If the goal is `x ∈ sᶜ ∪ tᶜ`:
```
by_contra h
-- h : ¬(x ∈ sᶜ ∪ tᶜ)
push_neg at h
-- h : x ∈ s ∧ x ∈ t
```

## Warning
`by_contra` uses classical logic (the law of excluded middle).
Every Lean proof may use it — there is no constructivity restriction.
-/
TacticDoc by_contra

/-- `Set.compl_inter` states `(s ∩ t)ᶜ = sᶜ ∪ tᶜ` (dual De Morgan). -/
TheoremDoc Set.compl_inter as "Set.compl_inter" in "Set"

/-- `compl_inf` is the lattice version: `(a ⊓ b)ᶜ = aᶜ ⊔ bᶜ`. -/
TheoremDoc compl_inf as "compl_inf" in "Set"

/-- `not_and_or` states `¬(a ∧ b) ↔ ¬a ∨ ¬b` (propositional dual De Morgan). -/
TheoremDoc not_and_or as "not_and_or" in "Set"

NewTactic by_contra
NewTheorem Set.compl_inter

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_inter compl_inf not_and_or
