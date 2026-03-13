import Game.Metadata

World "NormalPset"
Level 4

Title "Product Conjugation"

Introduction
"
Given `a ∈ N` and `b ∈ N`, prove that `g * a * b * g⁻¹ ∈ N`.

The key insight: treat `a * b` as a single element of `N` (since
`N` is closed under multiplication), then apply `conj_mem`.

There's one wrinkle: Lean parses `g * a * b * g⁻¹` as
`((g * a) * b) * g⁻¹`, but `conj_mem` produces
`(g * (a * b)) * g⁻¹`. You'll need `mul_assoc` to bridge the gap.
"

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a b g : G) (ha : a ∈ N) (hb : b ∈ N) :
    g * a * b * g⁻¹ ∈ N := by
  Hint "First, combine `a` and `b` into a single element of `N`:
  `have hab := N.mul_mem {ha} {hb}`."
  Branch
    rw [mul_assoc g a b]
    exact hN.conj_mem (a * b) (N.mul_mem ha hb) g
  Branch
    have h := hN.conj_mem a ha g
    Hint "You conjugated just `a`, getting `{h} : g * a * g⁻¹ ∈ N`.
    But the goal has `g * a * b * g⁻¹` — a product of *two* elements
    being conjugated. You need to treat `a * b` as a single element.

    Start over: `have hab := N.mul_mem {ha} {hb}` to combine them."
    have hab := N.mul_mem ha hb
    have h2 := hN.conj_mem (a * b) hab g
    rw [← mul_assoc] at h2
    exact h2
  have hab := N.mul_mem ha hb
  Hint "Now `{hab} : a * b ∈ N`. Conjugate:
  `have h := hN.conj_mem (a * b) {hab} g`."
  have h := hN.conj_mem (a * b) hab g
  Hint "Now `{h} : g * (a * b) * g⁻¹ ∈ N`. But the goal has
  `g * a * b * g⁻¹`. These differ by associativity.
  Use `rw [← mul_assoc] at {h}` to convert."
  rw [← mul_assoc] at h
  Hint (hidden := true) "`exact {h}`."
  exact h

Conclusion
"
The twist: `conj_mem` works on a single element, so you must group
`a * b` first via `mul_mem`. Then `← mul_assoc` reconciles Lean's
left-associative parsing.

On paper: *Since `a, b ∈ N`, we have `ab ∈ N` (closure under
multiplication). Then `g(ab)g⁻¹ ∈ N` by normality.*

Lean doesn't care about parenthesization on paper, but in the proof
assistant, `g * a * b * g⁻¹` and `g * (a * b) * g⁻¹` are different
expressions that `mul_assoc` relates.
"
