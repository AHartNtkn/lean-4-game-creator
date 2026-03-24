import Game.Metadata

World "SetOpsWorld"
Level 12

Title "Pushing Negation"

Introduction "
# The push_neg Tactic

When working with complements, you often encounter negated
propositions: `¬(P ∨ Q)`, `¬(P ∧ Q)`, `¬(∀ x, P x)`, etc.
You *could* break these apart manually, but there is a faster way.

The `push_neg` tactic pushes negation through logical connectives
using standard equivalences:

| Before push_neg | After push_neg |
|---|---|
| `¬(P ∨ Q)` | `¬P ∧ ¬Q` |
| `¬(P ∧ Q)` | `P → ¬Q` |
| `¬(∀ x, P x)` | `∃ x, ¬P x` |
| `¬(a < b)` | `b ≤ a` |

You can apply it to a hypothesis with `push_neg at h`, or to the
goal with just `push_neg`.

**Your task**: Prove that the complement of a union is contained in
the intersection of the complements. This is one direction of
**De Morgan's law** for sets:

$$(s \\cup t)^c \\subseteq s^c \\cap t^c$$

After `intro x hx`, you will have `hx : x ∈ (s ∪ t)ᶜ`, which is
definitionally `¬(x ∈ s ∨ x ∈ t)`. Use `change` to make the negated
disjunction explicit, then `push_neg` to convert it to
`x ∉ s ∧ x ∉ t` — which matches the goal.

**Why `change` is needed here**: Lean displays `hx : x ∈ (s ∪ t)ᶜ`
using set-theoretic complement notation, but `push_neg` needs to see
the negation explicitly as `¬(x ∈ s ∨ x ∈ t)`. The tactic
`change ¬(x ∈ s ∨ x ∈ t) at hx` converts to this definitionally
equal logical form so `push_neg` can process it. This
`change` + `push_neg` pattern will recur whenever you work with
complements of compound sets.
"

/-- The complement of a union is a subset of the intersection of
complements (one direction of De Morgan). -/
Statement (α : Type) (s t : Set α) : (s ∪ t)ᶜ ⊆ sᶜ ∩ tᶜ := by
  Hint "Start with `intro x hx` for the subset proof."
  intro x hx
  Hint "`hx` says `x` is in the complement of the union: `x ∉ s ∪ t`,
  which is `¬(x ∈ s ∨ x ∈ t)`. To make this explicit, use
  `change ¬(x ∈ s ∨ x ∈ t) at hx`."
  Branch
    -- Manual proof without push_neg
    constructor
    · Hint (hidden := true) "You need `x ∈ sᶜ`, which is `x ∉ s`.
      Use `intro hs` then `exact hx (Or.inl hs)`."
      intro hs
      exact hx (Or.inl hs)
    · Hint (hidden := true) "You need `x ∈ tᶜ`, which is `x ∉ t`.
      Use `intro ht` then `exact hx (Or.inr ht)`."
      intro ht
      exact hx (Or.inr ht)
  change ¬(x ∈ s ∨ x ∈ t) at hx
  Hint "Now `hx : ¬(x ∈ s ∨ x ∈ t)`. Use `push_neg at hx` to
  convert the negated disjunction to a conjunction of negations."
  Hint (hidden := true) "`push_neg at hx` transforms
  `¬(x ∈ s ∨ x ∈ t)` into `x ∉ s ∧ x ∉ t`.
  Then `exact hx` closes the goal."
  push_neg at hx
  Hint "`hx` is now `x ∉ s ∧ x ∉ t`, which matches the goal
  `x ∈ sᶜ ∩ tᶜ` (since `ᶜ` means `¬` and `∩` means `∧`).
  Use `exact hx`."
  exact hx

Conclusion "
You used `push_neg` to convert a negated disjunction into a conjunction
of negations:

$$\\neg(P \\lor Q) \\;\\;\\longrightarrow\\;\\; \\neg P \\;\\land\\; \\neg Q$$

This is the propositional De Morgan law, which `push_neg` applies
automatically. The tactic handles much more than this — it can push
negation through `∧`, `∨`, `→`, `∀`, `∃`, and arithmetic comparisons.

**Key workflow**: When you encounter a negated compound proposition
(in a hypothesis or goal):
1. `change` to make the negation explicit (if needed)
2. `push_neg` to simplify

In the next level, you will prove the full De Morgan equality
`(s ∪ t)ᶜ = sᶜ ∩ tᶜ` using `ext`, `push_neg`, and case analysis.
"

/-- `push_neg` pushes negation through logical connectives.

## Syntax
```
push_neg           -- simplify negation in the goal
push_neg at h      -- simplify negation in hypothesis h
```

## Transformations
| Before | After |
|---|---|
| `¬(P ∨ Q)` | `¬P ∧ ¬Q` |
| `¬(P ∧ Q)` | `P → ¬Q` |
| `¬(∀ x, P x)` | `∃ x, ¬P x` |
| `¬(∃ x, P x)` | `∀ x, ¬P x` |
| `¬(a < b)` | `b ≤ a` |

## When to use it
When a hypothesis or goal contains a negated compound proposition
that you want to simplify. Especially useful with complement
membership (`sᶜ` = `¬`).
-/
TacticDoc push_neg

NewTactic push_neg
NewTheorem Or.inl Or.inr

/-- `Set.compl_union` states `(s ∪ t)ᶜ = sᶜ ∩ tᶜ` (De Morgan). -/
TheoremDoc Set.compl_union as "Set.compl_union" in "Set"

/-- `compl_sup` is the lattice version of De Morgan: `(a ⊔ b)ᶜ = aᶜ ⊓ bᶜ`. -/
TheoremDoc compl_sup as "compl_sup" in "Set"

/-- `not_or` states `¬(a ∨ b) ↔ ¬a ∧ ¬b` (propositional De Morgan). -/
TheoremDoc not_or as "not_or" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_union compl_sup not_or
