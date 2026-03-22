import Game.Metadata

World "Powerset"
Level 7

Title "Powerset Monotonicity: The Converse"

Introduction "
# Bigger Powerset Means Bigger Set

Level 6 proved the forward direction: if $s \\subseteq t$ then
$\\mathcal{P}(s) \\subseteq \\mathcal{P}(t)$. Now prove the **converse**:

$$s.\\text{powerset} \\subseteq t.\\text{powerset} \\implies s \\subseteq t$$

This means powerset monotonicity is an equivalence — the powerset
*exactly reflects* the subset ordering.

**Key insight**: The set `s` itself is a member of `s.powerset`
(Level 2). If `s.powerset ⊆ t.powerset`, then `s` must also be in
`t.powerset`, which means `s ⊆ t`.

**Your task**: Given `h : s.powerset ⊆ t.powerset`, prove `s ⊆ t`.

You'll use:
- `have` to establish that `s ∈ s.powerset` (Level 2 pattern)
- Function application to get `s ∈ t.powerset`
- `rw [mem_powerset] at ...` to extract the subset fact (Level 5 pattern)
"

/-- If s.powerset ⊆ t.powerset, then s ⊆ t. -/
Statement (s t : Finset ℕ) (h : s.powerset ⊆ t.powerset) : s ⊆ t := by
  Hint "First, establish that `s ∈ s.powerset`. Use `have` to state
  this and prove it with `rw [Finset.mem_powerset]` (the Level 2 pattern)."
  Hint (hidden := true) "Try `have hs : s ∈ s.powerset := by rw [Finset.mem_powerset]`."
  have hs : s ∈ s.powerset := by rw [Finset.mem_powerset]
  Hint "Now use the hypothesis `h : s.powerset ⊆ t.powerset` to
  conclude that `s ∈ t.powerset`. Apply `h` to `hs`."
  Hint (hidden := true) "Try `have ht := h hs`."
  have ht := h hs
  Hint "You have `ht : s ∈ t.powerset`. Extract the subset fact
  with `rw [Finset.mem_powerset] at ht` (the Level 4 pattern)."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : s ⊆ t`, which is exactly the goal."
  Hint (hidden := true) "Try `exact ht`."
  exact ht

Conclusion "
You proved the converse of powerset monotonicity:

$$s.\\text{powerset} \\subseteq t.\\text{powerset} \\implies s \\subseteq t$$

**The insight**: The set `s` *witnesses* the inclusion — it is in
`s.powerset`, so it must be in `t.powerset`, which means `s ⊆ t`.

**Proof recipe**:
1. `have hs : s ∈ s.powerset := by rw [mem_powerset]` — witness
2. `have ht := h hs` — transport via the inclusion
3. `rw [mem_powerset] at ht` — extract the subset
4. `exact ht` — close

Combined with Level 6, this gives an **equivalence**:

$$s \\subseteq t \\iff \\mathcal{P}(s) \\subseteq \\mathcal{P}(t)$$

The powerset operation is an *order embedding*: it exactly preserves
the subset ordering. This is a deeper fact than either direction alone.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
