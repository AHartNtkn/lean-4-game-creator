import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 4

Title "Extracting a witness from a nonempty finset"

Introduction
"
# From nonempty to witness

Before we can state the pigeonhole principle, we need two proof moves
that connect cardinality to existence and emptiness. This level covers
the first: **extracting a witness from a nonempty finset**.

## The move

If you know `s.Nonempty` for a finset `s`, this means `∃ x, x ∈ s`.
In fact, `Finset.Nonempty s` is *defined* as `∃ x, x ∈ s`. So you can
destructure it with `obtain`:
```
obtain ⟨x, hx⟩ := h
```
This gives you a concrete element `x` and a proof `hx : x ∈ s`.

## Your task

Given a nonempty finset `s`, produce an element of `s` and a proof that
it belongs to `s`.
"

/-- If `s` is nonempty, then there exists an element in `s`. -/
Statement (s : Finset ℕ) (h : s.Nonempty) : ∃ x, x ∈ s := by
  Hint "The hypothesis `h : s.Nonempty` is definitionally `∃ x, x ∈ s`.
  You can destructure it with `obtain ⟨x, hx⟩ := h` to get a witness
  `x` and proof `hx : x ∈ s`."
  obtain ⟨x, hx⟩ := h
  Hint "Now you have `x : ℕ` and `hx : x ∈ s`. The goal is `∃ x, x ∈ s`.
  Use `exact ⟨x, hx⟩` to provide the witness."
  exact ⟨x, hx⟩

Conclusion
"
The proof destructured `s.Nonempty` (which is `∃ x, x ∈ s`) to extract
a concrete witness.

## The proof move: obtain on existentials

`obtain ⟨x, hx⟩ := h` is the standard way to \"open\" an existential
hypothesis in Lean. After this tactic:
- `x` is a term of the appropriate type,
- `hx` is a proof of the predicate applied to `x`.

This move appears constantly in combinatorial arguments: \"since the set
is nonempty, pick an element from it.\"

## Alternative proof

Since `Finset.Nonempty s` is definitionally `∃ x, x ∈ s`, you could
also have used `exact h` directly. But the `obtain` version is more
instructive because it mirrors the mathematical reasoning: \"let `x`
be an element of `s`, with `hx` witnessing membership.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
