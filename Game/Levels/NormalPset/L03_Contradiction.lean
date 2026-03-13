import Game.Metadata

World "NormalPset"
Level 3

Title "Contradiction"

Introduction
"
Sometimes a proof works by deriving a contradiction. The
`contradiction` tactic closes any goal when the context contains
hypotheses that contradict each other — for example, `h : a ∈ N`
and `h' : a ∉ N`.

Here, you know `a ∈ N` and `N` is normal. You also know that
`g * a * g⁻¹ ∉ N`. But normality guarantees `g * a * g⁻¹ ∈ N` —
contradiction!

Derive the positive fact with `have`, then use `contradiction`.
"

/-- `contradiction` closes a goal when the context contains
contradictory hypotheses.

**Syntax**: `contradiction`

**When to use**: When you have both `h : P` and `h' : ¬P` (or
`h : a ∈ N` and `h' : a ∉ N`), `contradiction` closes any goal.

You may need `have` to derive one of the contradictory facts first.

**Example**: If the context has `ha : a ∈ N` and `hna : a ∉ N`,
then `contradiction` closes the goal immediately. -/
TacticDoc «contradiction»

NewTactic «contradiction»

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a g : G) (ha : a ∈ N) (hc : g * a * g⁻¹ ∉ N) : False := by
  Hint "You have `{ha} : a ∈ N`. Since `N` is normal, conjugation
  preserves membership. Derive the contradiction:
  `have h := hN.conj_mem a {ha} g`."
  have h := hN.conj_mem a ha g
  Hint "Now `{h} : g * a * g⁻¹ ∈ N` and `{hc} : g * a * g⁻¹ ∉ N`.
  These contradict each other. Use `contradiction`."
  contradiction

Conclusion
"
The **contradiction-setup** move:

1. Derive the positive fact (here, `g * a * g⁻¹ ∈ N` via `conj_mem`)
2. `contradiction` closes the goal

On paper: *Since `a ∈ N` and `N` is normal, `gag⁻¹ ∈ N` —
contradicting `gag⁻¹ ∉ N`.*

The `contradiction` tactic is a finishing move: it handles the last
step once you've established that the hypotheses are contradictory.
The real work is always in step 1 — deriving the contradictory fact.
"
