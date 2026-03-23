import Game.Metadata

World "PsetSets"
Level 8

Title "Nonempty Product Converse"

TheoremTab "Set"

Introduction "
# Problem Set: Level 8

In Indexed Operations World, you proved that nonempty sets have a
nonempty product. Prove the **converse**: if a cartesian product is
nonempty, then BOTH factors are nonempty.

$$\\text{Nonempty}(s \\times^s t) \\;\\Longrightarrow\\;
\\text{Nonempty}(s) \\;\\wedge\\; \\text{Nonempty}(t)$$

The proof extracts a pair from the product, unpacks the product
membership, and uses the components as witnesses for each factor.
"

/-- If a cartesian product is nonempty, both factors are nonempty. -/
Statement (α : Type) (β : Type) (s : Set α) (t : Set β)
    (h : Set.Nonempty (s ×ˢ t)) : Set.Nonempty s ∧ Set.Nonempty t := by
  Hint "Unpack `h : Set.Nonempty (s ×ˢ t)` to get a witness pair.
  Use `obtain ⟨p, hp⟩ := h`."
  obtain ⟨p, hp⟩ := h
  Hint "Now `p : α × β` and `hp : p ∈ s ×ˢ t`. Convert the product
  membership with `rw [Set.mem_prod] at hp`."
  rw [Set.mem_prod] at hp
  Hint "You have `hp : p.1 ∈ s ∧ p.2 ∈ t`. Destructure and build
  the two nonemptiness proofs."
  Hint (hidden := true) "Key move: `obtain` splits `hp`, then each
  component is a witness for `Set.Nonempty`."
  obtain ⟨hps, hpt⟩ := hp
  constructor
  · exact ⟨p.1, hps⟩
  · exact ⟨p.2, hpt⟩

Conclusion "
You proved the converse of the nonempty product theorem. The proof
combined:
- `obtain` to extract the witness pair from `Set.Nonempty`
- `rw [Set.mem_prod]` to convert product membership to a conjunction
- `obtain` again to split the conjunction
- Projections `p.1` and `p.2` to provide witnesses for each factor

In ordinary math: if $(a, b) \\in s \\times t$, then $a \\in s$ and
$b \\in t$, so both sets are nonempty.

Together with the result from Indexed Operations World, this gives the
full equivalence: $s \\times^s t$ is nonempty if and only if both $s$ and
$t$ are nonempty.
"

/-- `Set.prod_nonempty_iff` characterizes `(s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty`. -/
TheoremDoc Set.prod_nonempty_iff as "Set.prod_nonempty_iff" in "Set"

/-- `Set.Nonempty.fst` extracts nonemptiness of the first factor. -/
TheoremDoc Set.Nonempty.fst as "Set.Nonempty.fst" in "Set"

/-- `Set.Nonempty.snd` extracts nonemptiness of the second factor. -/
TheoremDoc Set.Nonempty.snd as "Set.Nonempty.snd" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.prod_nonempty_iff Set.Nonempty.fst Set.Nonempty.snd
