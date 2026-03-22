import Game.Metadata

World "Powerset"
Level 8

Title "Powerset Monotonicity: The Equivalence"

Introduction "
# Combining Both Directions

Level 6 proved the forward direction:
$$s \\subseteq t \\implies \\mathcal{P}(s) \\subseteq \\mathcal{P}(t)$$

Level 7 proved the converse:
$$\\mathcal{P}(s) \\subseteq \\mathcal{P}(t) \\implies s \\subseteq t$$

Now combine them into the full equivalence using `constructor`
to split an `iff` goal into its two directions.

**Your task**: Prove `s.powerset ⊆ t.powerset ↔ s ⊆ t`.

The two directions are exactly the proofs from Level 7 (first)
and Level 6 (second). Use `constructor` to split, then reproduce
each direction.
"

/-- Powerset inclusion is equivalent to subset inclusion. -/
Statement (s t : Finset ℕ) : s.powerset ⊆ t.powerset ↔ s ⊆ t := by
  Hint "The goal is an `iff` (`↔`). Use `constructor` to split it into
  the forward direction and the backward direction."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Forward: powerset inclusion → subset (Level 7 pattern)
  Hint "**Forward direction**: Prove `s.powerset ⊆ t.powerset → s ⊆ t`.
  Start with `intro h` to assume the powerset inclusion."
  Hint (hidden := true) "Try `intro h`."
  intro h
  Hint "Now use the Level 7 pattern: establish `s ∈ s.powerset`,
  transport via `h`, then extract the subset fact."
  Hint (hidden := true) "Try `have hs : s ∈ s.powerset := by rw [Finset.mem_powerset]`."
  have hs : s ∈ s.powerset := by rw [Finset.mem_powerset]
  Hint (hidden := true) "Try `have ht := h hs`."
  have ht := h hs
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint (hidden := true) "Try `exact ht`."
  exact ht
  -- Backward: subset → powerset inclusion (Level 6 pattern)
  Hint "**Backward direction**: Prove `s ⊆ t → s.powerset ⊆ t.powerset`.
  Start with `intro h` to assume the subset."
  Hint (hidden := true) "Try `intro h`."
  intro h
  Hint "Now use the Level 6 pattern: introduce an element `u` of
  `s.powerset`, convert both sides to subset claims, then chain."
  Hint (hidden := true) "Try `intro u hu`."
  intro u hu
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at hu ⊢`."
  rw [Finset.mem_powerset] at hu ⊢
  Hint (hidden := true) "Try `intro x hx`."
  intro x hx
  Hint (hidden := true) "Try `exact h (hu hx)`."
  exact h (hu hx)

Conclusion "
You proved the full equivalence:

$$s \\subseteq t \\iff \\mathcal{P}(s) \\subseteq \\mathcal{P}(t)$$

The powerset operation is an **order embedding**: it exactly
preserves the subset ordering. This is a deeper structural fact
than either direction alone.

**Proof structure**:
- `constructor` splits the iff into two implications
- Forward direction: the Level 7 witness argument
- Backward direction: the Level 6 monotonicity argument

**Pattern**: When you've proved both directions of an equivalence
in separate levels, `constructor` lets you combine them. This
pattern appears throughout mathematics: prove the forward and
reverse implications, then package them as an iff.

**Library comparison**: Mathlib packages this equivalence as
`Finset.powerset_mono`. Your multi-step proof established both
directions from first principles. The library version is the
one-liner, but now you understand *why* it's true — the forward
direction chains subset hypotheses, and the converse uses the
witness `s ∈ s.powerset`.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
