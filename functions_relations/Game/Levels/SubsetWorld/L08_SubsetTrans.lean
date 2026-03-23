import Game.Metadata

World "SubsetWorld"
Level 8

Title "Subset Transitivity"

Introduction "
# Chaining Subsets

If $A \\subseteq B$ and $B \\subseteq C$, then $A \\subseteq C$. This is
**transitivity** of the subset relation.

In Level 6, you learned that a subset hypothesis `h : s ⊆ t` acts as
a function: given a proof that `x ∈ s`, it returns a proof that
`x ∈ t`. Now you will **chain** two such function applications to
prove transitivity.

There are two natural proof strategies:

**Backward (with `apply`)**: Start from the goal `x ∈ u` and work
backward. `apply htu` reduces the goal to `x ∈ t` (since `htu` says
\"if in `t`, then in `u`\"). Then `apply hst` reduces to `x ∈ s`.
Then `exact hx` closes it.

**Forward (with `have`)**: Start from `hx : x ∈ s` and work forward.
`have hxt := hst hx` gives `hxt : x ∈ t`. Then
`have hxu := htu hxt` gives `hxu : x ∈ u`. Then `exact hxu`.

Try the backward approach — it is shorter and builds your `apply` skills.
"

/-- Subset inclusion is transitive. -/
Statement (α : Type) (s t u : Set α) (hst : s ⊆ t) (htu : t ⊆ u) :
    s ⊆ u := by
  Hint "Start with `intro x hx` as always for a `⊆` proof."
  intro x hx
  Branch
    have hxt : x ∈ t := hst hx
    Hint "Good — you derived `x ∈ t` from `hx` and `hst`. Now use
    `htu` similarly: `exact htu hxt` or `have hxu := htu hxt`."
    exact htu hxt
  Branch
    have hxt := hst hx
    Hint "You have `hxt : x ∈ t`. Now use `htu` to get `x ∈ u`:
    either `exact htu hxt` or `have hxu := htu hxt` then `exact hxu`."
    exact htu hxt
  Branch
    exact htu (hst hx)
    -- One-liner combining both applications
  Hint "The goal is `x ∈ u`. You know `htu : t ⊆ u`, which says
  anything in `t` is in `u`. Use `apply htu` — this reduces the
  goal to `x ∈ t`."
  Hint (hidden := true) "`apply htu` matches the conclusion `x ∈ u`
  against the output of `htu` and leaves `x ∈ t` as the new goal."
  apply htu
  Hint "Now the goal is `x ∈ t`. Use `apply hst` to reduce it to
  `x ∈ s`."
  apply hst
  Hint "The goal is `x ∈ s` and you have `hx : x ∈ s`. Use `exact hx`."
  exact hx

Conclusion "
Subset transitivity chains: from `s ⊆ t` and `t ⊆ u`, you derive
`s ⊆ u` by composing the two inclusions.

The backward proof with `apply`:
```
apply htu    -- goal: x ∈ u → x ∈ t
apply hst    -- goal: x ∈ t → x ∈ s
exact hx     -- done
```

Notice how `apply` traces the chain in reverse: to prove `x ∈ u`,
first reduce to `x ∈ t`, then to `x ∈ s`. This is backward reasoning —
working from the goal toward what you know.

The forward alternative `exact htu (hst hx)` composes the functions
directly: `hst hx` gives `x ∈ t`, then `htu` applied to that gives
`x ∈ u`. Both styles are valid; use whichever feels natural.

The library name is `Set.Subset.trans`.

**Discovery tool**: When you are unsure which lemma closes the current
goal, try typing `exact?` in your proof. It searches the library for
a term that matches the goal. For instance, if the goal is
`s ⊆ u` and you have `hst` and `htu` in context, `exact?` might
suggest `exact Set.Subset.trans hst htu`. This becomes increasingly
useful as the API grows in later worlds.
"

/-- `Set.Subset.trans` proves `s ⊆ t → t ⊆ u → s ⊆ u` (subset transitivity). -/
TheoremDoc Set.Subset.trans as "Set.Subset.trans" in "Set"

/-- `le_trans` proves `a ≤ b → b ≤ c → a ≤ c` for any preorder.
For sets, `≤` is `⊆`, so this is transitivity of subset inclusion. -/
TheoremDoc le_trans as "le_trans" in "Set"

/-- `LE.le.trans` is the dot-notation form of `le_trans`:
`hab.trans hbc` proves `a ≤ c` from `hab : a ≤ b` and `hbc : b ≤ c`. -/
TheoremDoc LE.le.trans as "LE.le.trans" in "Set"

NewTheorem Set.Subset.trans

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.Subset.trans le_trans LE.le.trans HasSubset.Subset.trans Trans.trans Preorder.le_trans Set.mem_setOf_eq Set.mem_setOf
