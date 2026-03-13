import Game.Metadata

World "NormalDef"
Level 3

Title "The have Tactic"

Introduction
"
Sometimes a theorem gives you *almost* what you need, but with a slight
difference. The `have` tactic lets you store an intermediate result as a
named hypothesis, then modify it.

**Syntax**: `have h := expr` creates a new hypothesis `h` with the
value of `expr`. After `have`, you can `rw` at `h` to clean it up.

Here's the situation: you know `N` is normal. You know
`hN.conj_mem n hn g` gives `g * n * g⁻¹ ∈ N` for any conjugator `g`.

But the goal asks for `g⁻¹ * n * g ∈ N` — conjugation by `g⁻¹`, not
by `g`. You could use `g⁻¹` as the conjugator in `conj_mem`, but then
you'd get `g⁻¹ * n * (g⁻¹)⁻¹ ∈ N`, which has `(g⁻¹)⁻¹` instead of
`g`. Use `have` to save this intermediate, then `rw [inv_inv]` to fix it.
"

/-- `have` introduces an intermediate result into your proof.

**Basic form**: `have h := expr` — creates hypothesis `h` with the
value of `expr`.

**Typed form**: `have h : T := expr` — creates hypothesis `h : T`.

After `have`, the new hypothesis appears in your context and you can
use `rw`, `exact`, or `apply` with it.

Example: `have h := hN.conj_mem n hn g` creates
`h : g * n * g⁻¹ ∈ N`. -/
TacticDoc «have»

NewTactic «have»

/-- `conj_mem'` is the reverse-conjugation variant:

`hN.conj_mem' n hn g : g⁻¹ * n * g ∈ N`

where `hN : N.Normal`, `hn : n ∈ N`, and `g : G`.

Use this when the conjugator appears inverted. -/
TheoremDoc Subgroup.Normal.conj_mem' as "conj_mem'" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem Subgroup.Normal.conj_mem'

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (n : G) (hn : n ∈ N) (g : G) : g⁻¹ * n * g ∈ N := by
  Hint "The goal is `g⁻¹ * n * g ∈ N`. You know `conj_mem` works with
  any conjugator. Using `g⁻¹` as the conjugator gives
  `g⁻¹ * n * (g⁻¹)⁻¹ ∈ N` — almost right, but `(g⁻¹)⁻¹` isn't `g`.

  Use `have` to store the intermediate:
  `have h := hN.conj_mem n hn g⁻¹`."
  have h := hN.conj_mem n hn g⁻¹
  Hint "Now `{h} : g⁻¹ * n * (g⁻¹)⁻¹ ∈ N`. Clean up `(g⁻¹)⁻¹` to `g`:
  `rw [inv_inv] at {h}`."
  rw [inv_inv] at h
  Hint (hidden := true) "Now `{h} : g⁻¹ * n * g ∈ N` — exactly the goal.
  `exact {h}`."
  exact h

Conclusion
"
The `have` tactic is essential when a theorem gives you *almost* what
you need. This is the **store-and-clean** pattern:

1. `have h := theorem_application` — store the raw result
2. `rw [...] at h` — clean it up
3. `exact h` — close the goal

Without `have`, you would need an elaborate one-liner like
`exact inv_inv g ▸ hN.conj_mem n hn g⁻¹` — much harder to read
and write.

You also proved `conj_mem'`: normality gives conjugation by the
inverse for free. This result enters your inventory starting next level.

On paper: *Since `N` is normal, conjugating `n ∈ N` by `g⁻¹` gives
`g⁻¹ n (g⁻¹)⁻¹ = g⁻¹ n g ∈ N`.*

The `have` tactic will appear constantly from now on. Every time you
need an intermediate result — a calculation, a membership proof, a
rewritten hypothesis — `have` is the tool.
"
