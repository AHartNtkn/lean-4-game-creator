import Game.Metadata

World "HomBasics"
Level 2

Title "The `specialize` Tactic"

Introduction
"
You have a hypothesis `h : ∀ x : G, x ∈ f.ker` — every element
of `G` is in the kernel. You need to show `f a = 1` for a
specific element `a`.

The hypothesis `h` talks about *all* elements, but you need it
for *one particular* element. The `specialize` tactic does this:

`specialize h a`

replaces `h : ∀ x : G, x ∈ f.ker` with `h : a ∈ f.ker` —
pinning the universal statement to the specific value `a`.

Then use the kernel-reasoning move to finish.
"

/-- `specialize h a₁ a₂ ...` replaces a universally quantified
hypothesis `h : ∀ x₁ x₂ ..., P x₁ x₂ ...` with the specialized
version `h : P a₁ a₂ ...`.

**Example**: if `h : ∀ x : G, x ∈ f.ker`, then `specialize h a`
gives `h : a ∈ f.ker`.

**Warning**: `specialize` is destructive — it replaces the original
hypothesis. If you might need the universal version later, consider
using `have h' := h a` instead (once you learn `have`). -/
TacticDoc specialize

NewTactic specialize

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a : G)
    (h : ∀ x : G, x ∈ f.ker) : f a = 1 := by
  Hint "You have `{h} : ∀ x : G, x ∈ f.ker` — a fact about every
  element. Use `specialize {h} a` to pin it to the element `a`."
  specialize h a
  Hint "Now `{h} : a ∈ f.ker`. Unfold the kernel membership:
  `rw [MonoidHom.mem_ker] at {h}`."
  rw [MonoidHom.mem_ker] at h
  Hint (hidden := true) "Now `{h} : f a = 1`. Use `exact {h}`."
  exact h

Conclusion
"
The `specialize` tactic takes a universal hypothesis and pins it to
a specific value. The pattern is:

1. `specialize h a` — instantiate `∀ x, ...` to the specific `a`
2. `rw [MonoidHom.mem_ker] at h` — unfold kernel membership
3. Use `h` directly

This `specialize` → `rw [mem_ker] at h` → use `h` pattern is
the **kernel-reasoning move** applied to hypotheses.

One warning: `specialize` is destructive — it replaces the original
`∀`-hypothesis with the specialized version. If you need the
universal version again later, you'd want to make a copy first
(you'll learn `have` for this later).
"
