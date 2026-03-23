import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 22

Title "Indexed Intersection Distributes over Union"

Introduction "
# The Dual Distributive Law

In the boss (next level), you will prove that indexed union distributes
over intersection: $(\\bigcup_i s_i) \\cap t = \\bigcup_i (s_i \\cap t)$.
Here, prove the **dual**: indexed intersection distributes over union.

$$(\\bigcap_i s_i) \\cup t = \\bigcap_i (s_i \\cup t)$$

This says: being in every `s i` OR in `t` is the same as being in
every `s i ∪ t`.

This level integrates `Set.mem_iInter` with `Set.mem_union` and
requires case analysis on the union. The **backward direction** needs
`by_cases` — the classical principle of case analysis — because
knowing `x ∈ s i ∪ t` for every `i` does not directly tell you which
disjunct holds globally.

**About `by_cases`**: `by_cases h : P` splits the proof into two
branches: one where `h : P` holds, and one where `h : ¬P` holds.
This is weaker than `by_contra` (which assumes the negation of the
whole goal). You used `by_contra` in the De Morgan levels; `by_cases`
is the same classical reasoning applied to a specific proposition.
"

/-- `by_cases h : P` splits the proof into two branches: one where
`h : P` holds, and one where `h : ¬P` holds.

## Syntax
```
by_cases h : P
```

## When to use it
When you need to consider two cases based on whether a proposition
is true or false. Unlike `cases` (which splits a hypothesis), `by_cases`
creates the case split from nothing — it is classical reasoning.

## Example
```
by_cases h : x ∈ t
· -- h : x ∈ t
  ...
· -- h : x ∉ t
  ...
```
-/
TacticDoc by_cases

NewTactic by_cases
NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- Indexed intersection distributes over union. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (t : Set α) :
    (⋂ i, s i) ∪ t = ⋂ i, (s i ∪ t) := by
  Hint "Start with `ext x` to reduce to a membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔`."
  constructor
  -- Forward: x ∈ (⋂ i, s i) ∪ t → x ∈ ⋂ i, (s i ∪ t)
  · Hint "**Forward direction**: Assume `x ∈ (⋂ i, s i) ∪ t` and prove
    `x ∈ ⋂ i, (s i ∪ t)`.

    Start with `intro hx`. Then rewrite the goal to a universal
    with `rw [Set.mem_iInter]` and introduce the index."
    intro hx
    Hint "Rewrite the goal: `rw [Set.mem_iInter]` to get
    `∀ i, x ∈ s i ∪ t`."
    rw [Set.mem_iInter]
    Hint "Use `intro i` to introduce the index."
    intro i
    Hint "The goal is `x ∈ s i ∪ t`. You have `hx : x ∈ (⋂ i, s i) ∪ t`.
    Split `hx` into cases — `x` is either in the intersection or in `t`.

    Use `cases hx with | inl hinter | inr ht`."
    Hint (hidden := true) "`cases hx with | inl hinter | inr ht` creates
    two subgoals: one where `hinter : x ∈ ⋂ i, s i`, and one where
    `ht : x ∈ t`."
    cases hx with
    | inl hinter =>
      Hint "You have `hinter : x ∈ ⋂ i, s i`. Rewrite to a universal:
      `rw [Set.mem_iInter] at hinter`. Then `left` and `exact hinter i`."
      Hint (hidden := true) "`rw [Set.mem_iInter] at hinter` then `left`
      then `exact hinter i`."
      rw [Set.mem_iInter] at hinter
      left
      exact hinter i
    | inr ht =>
      Hint "You have `ht : x ∈ t`. The goal is `x ∈ s i ∪ t`. Since
      `x ∈ t`, use `right` then `exact ht`."
      Hint (hidden := true) "`right` then `exact ht`."
      right
      exact ht
  -- Backward: x ∈ ⋂ i, (s i ∪ t) → x ∈ (⋂ i, s i) ∪ t
  · Hint "**Backward direction (classical)**: You have
    `x ∈ ⋂ i, (s i ∪ t)`, meaning `∀ i, x ∈ s i ∨ x ∈ t`. You must
    show `x ∈ (⋂ i, s i) ∪ t`, which is `x ∈ ⋂ i, s i ∨ x ∈ t`.

    The difficulty: knowing that `x ∈ s i ∨ x ∈ t` for EACH `i`
    separately does not tell you which disjunct holds uniformly. You
    need `by_cases` on `x ∈ t` to resolve this.

    Start with `intro hx` and then `rw [Set.mem_iInter] at hx`."
    intro hx
    rw [Set.mem_iInter] at hx
    Hint "Now `hx : ∀ i, x ∈ s i ∪ t`. Use `by_cases ht : x ∈ t` to
    split into two cases."
    Hint (hidden := true) "`by_cases ht : x ∈ t` — if `x ∈ t`, go right;
    if `x ∉ t`, show `x ∈ ⋂ i, s i` using `hx`."
    by_cases ht : x ∈ t
    · Hint "You have `ht : x ∈ t`. Use `right` then `exact ht`."
      right
      exact ht
    · Hint "You have `ht : x ∉ t`. Since for every `i`, either `x ∈ s i`
      or `x ∈ t`, and `x ∉ t`, it must be that `x ∈ s i` for every `i`.
      So `x ∈ ⋂ i, s i`.

      Use `left` then `rw [Set.mem_iInter]` then `intro i`."
      left
      rw [Set.mem_iInter]
      intro i
      Hint "The goal is `x ∈ s i`. Use `have hi := hx i` to get
      `hi : x ∈ s i ∪ t`, then split into cases."
      Hint (hidden := true) "`have hi := hx i` then `cases hi with | inl h | inr h`
      then `exact h` then `contradiction`."
      have hi := hx i
      cases hi with
      | inl h => exact h
      | inr h => contradiction

Conclusion "
You proved the dual distributive law:
$(\\bigcap_i s_i) \\cup t = \\bigcap_i (s_i \\cup t)$

This is the mirror image of the boss (next level), with `⋂`/`∪`
swapped for `⋃`/`∩`. Compare the two:

| Law | Set form | Quantifier form |
|---|---|---|
| Boss (next) | $(\\bigcup_i s_i) \\cap t = \\bigcup_i (s_i \\cap t)$ | `∃` distributes over `∧` |
| This level | $(\\bigcap_i s_i) \\cup t = \\bigcap_i (s_i \\cup t)$ | `∀` distributes over `∨` |

**Why the backward direction was harder**: The forward direction is
constructive — you just push the union through the intersection pointwise.
But the backward direction requires knowing whether `x ∈ t` globally
before you can extract `x ∈ s i` for each `i`. This is the same
classical/constructive asymmetry you saw in De Morgan (Level 19).

In ordinary math: \"If $x \\in s_i \\cup t$ for every $i$, either $x \\in t$
(and we are done) or $x \\notin t$, in which case $x \\in s_i$ for every
$i$, so $x \\in \\bigcap_i s_i$.\"
"

/-- `Set.iInter_union` states `(⋂ i, s i) ∪ t = ⋂ i, (s i ∪ t)`. -/
TheoremDoc Set.iInter_union as "Set.iInter_union" in "Set"

/-- `Set.union_iInter` states `t ∪ ⋂ i, s i = ⋂ i, (t ∪ s i)`. -/
TheoremDoc Set.union_iInter as "Set.union_iInter" in "Set"

/-- `iInf_sup_eq` is the lattice version of indexed intersection/union
distributivity. -/
TheoremDoc iInf_sup_eq as "iInf_sup_eq" in "Set"

/-- `sup_iInf_eq` is the lattice version (commuted order). -/
TheoremDoc sup_iInf_eq as "sup_iInf_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iInter_union Set.union_iInter iInf_sup_eq sup_iInf_eq
