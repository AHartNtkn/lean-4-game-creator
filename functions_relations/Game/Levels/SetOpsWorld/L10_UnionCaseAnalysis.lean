import Game.Metadata

World "SetOpsWorld"
Level 10

Title "Case Analysis on Unions"

Introduction "
# Case Analysis: Splitting a Union Hypothesis

So far you have been **proving** union membership (choosing `left` or
`right`). Now you must **use** a union hypothesis — when you KNOW
`x ∈ s ∪ t` and must derive something from it.

Since `x ∈ s ∪ t` is a disjunction, you handle it by **case analysis**:
consider the case `x ∈ s` and the case `x ∈ t` separately. The tactic
is `cases`:

```
cases h with | inl hs | inr ht
```

This creates two subgoals:
- **Case `inl`**: `hs : x ∈ s` in context (\"inject left\" — the left
  disjunct holds)
- **Case `inr`**: `ht : x ∈ t` in context (\"inject right\" — the right
  disjunct holds)

Handle each subgoal with a `·` prefix, just like after `constructor`.

**Your task**: Prove union commutativity at the element level. Given
`h : x ∈ s ∪ t`, prove `x ∈ t ∪ s`. You will need to \"swap sides\":
in the `inl` case (knowing `x ∈ s`), use `right`; in the `inr` case
(knowing `x ∈ t`), use `left`.
"

/-- If x is in s ∪ t, then x is in t ∪ s. -/
Statement (α : Type) (s t : Set α) (x : α) (h : x ∈ s ∪ t) :
    x ∈ t ∪ s := by
  Hint "Use `cases h with | inl hs | inr ht` to split the hypothesis
  into two cases: `x ∈ s` or `x ∈ t`."
  Hint (hidden := true) "After `cases h with | inl hs | inr ht`,
  you get two goals. Use `·` to handle each one.

  Case `inl` (have `hs : x ∈ s`): use `right` then `exact hs`.
  Case `inr` (have `ht : x ∈ t`): use `left` then `exact ht`."
  cases h with
  | inl hs =>
    Hint "You have `hs : x ∈ s` and need `x ∈ t ∪ s`. Since
    `s` is the RIGHT operand of `t ∪ s`, use `right`."
    Hint (hidden := true) "`right` then `exact hs`."
    right
    exact hs
  | inr ht =>
    Hint "You have `ht : x ∈ t` and need `x ∈ t ∪ s`. Since
    `t` is the LEFT operand of `t ∪ s`, use `left`."
    Hint (hidden := true) "`left` then `exact ht`."
    left
    exact ht

Conclusion "
You performed case analysis on a union hypothesis for the first time!

The pattern `cases h with | inl hs | inr ht` is the standard way to
handle any hypothesis that is a disjunction (or, equivalently, a union
membership). It creates two subgoals — one for each case — and you
handle them separately.

The names `inl` and `inr` stand for \"inject left\" and \"inject right\" —
the two constructors of `Or` (disjunction). They tell you which
branch of the `∨` holds:
- `| inl hs` — the LEFT disjunct holds (`x ∈ s`)
- `| inr ht` — the RIGHT disjunct holds (`x ∈ t`)

This pattern will appear again in De Morgan's law and the boss level.
It is the set-operation counterpart of the `cases` pattern you used
for natural numbers and existentials.

**Note**: You proved the element-level version `x ∈ s ∪ t → x ∈ t ∪ s`.
Combining this with `ext` gives the set equality `s ∪ t = t ∪ s`
(`Set.union_comm`). You will do exactly this in the next level.
"

/-- `Set.union_comm` states `s ∪ t = t ∪ s`. -/
TheoremDoc Set.union_comm as "Set.union_comm" in "Set"

/-- `sup_comm` is the lattice version of `s ∪ t = t ∪ s`. -/
TheoremDoc sup_comm as "sup_comm" in "Set"

/-- `Or.comm` states `a ∨ b ↔ b ∨ a` (propositional commutativity of ∨). -/
TheoremDoc Or.comm as "Or.comm" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.union_comm sup_comm Or.comm
