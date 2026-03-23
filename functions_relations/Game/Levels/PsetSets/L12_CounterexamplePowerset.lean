import Game.Metadata

World "PsetSets"
Level 12

Title "Counterexample: Powerset of Union"

TheoremTab "Set"

Introduction "
# Problem Set: Level 12

In Level 11, you proved `𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t` — the powerset
distributes over intersection. You might wonder: does it also
distribute over **union**?

The answer is **no**. Prove:

$$\\neg\\, (\\forall\\, s\\, t : \\text{Set}\\;\\mathbb{N},\\;
\\mathcal{P}(s \\cup t) = \\mathcal{P}\\, s \\cup \\mathcal{P}\\, t)$$

**Counterexample intuition**: Take `s = \\{0\\}` and `t = \\{1\\}`. Then
`s ∪ t = \\{0, 1\\}`, so `\\{0, 1\\} ∈ 𝒫(s ∪ t)` (it is a subset of
itself). But `\\{0, 1\\} ∉ 𝒫 s` (not a subset of `\\{0\\}`) and
`\\{0, 1\\} ∉ 𝒫 t` (not a subset of `\\{1\\}`). So the right side
misses a member of the left side.
"

/-- The powerset does NOT distribute over union. -/
Statement : ¬ (∀ s t : Set ℕ, 𝒫 (s ∪ t) = 𝒫 s ∪ 𝒫 t) := by
  Hint "Start with `intro h` to assume the universal statement, then
  specialize it to specific sets."
  intro h
  Hint "Specialize to the singletons containing 0 and 1. Apply `h`
  to these two sets to get a concrete equation."
  Hint (hidden := true) "Apply `h` to the two singleton sets to get
  a concrete equation. Then show the union of the two singletons is
  in the powerset of the union, rewrite using the equation, and
  derive a contradiction in each case."
  have h1 := h {0} {1}
  Hint "Show that the union of the two singletons is in the
  powerset of the union — it is a subset of itself."
  Hint (hidden := true) "Key move: declare `hmem` asserting the union of the two singletons is in its own powerset. Prove it with `rw [Set.mem_powerset_iff]` — this converts to a subset goal that closes automatically by reflexivity."
  have hmem : ({0} ∪ {1} : Set ℕ) ∈ 𝒫 ({0} ∪ {1}) := by
    rw [Set.mem_powerset_iff]
  Hint "Rewrite using the equation to move the membership to the
  right side."
  rw [h1] at hmem
  Hint "Case-split on which powerset the union belongs to."
  cases hmem with
  | inl hps =>
    Hint "This case says the union of singletons is a subset of the
    singleton containing just 0. But 1 is in the union, so 1 would
    have to equal 0 — contradiction."
    Hint (hidden := true) "Show 1 is in the union: `have h2 : (1 : N) ∈ ... := by right; rfl`. Then `have h3 := hps h2`, use `change` to expose the equality as `(1 : N) = 0`, and close with `omega`."
    have h2 : (1 : ℕ) ∈ ({0} ∪ {1} : Set ℕ) := by right; rfl
    have h3 := hps h2
    change (1 : ℕ) = 0 at h3
    omega
  | inr hpt =>
    Hint "This case says the union of singletons is a subset of the
    singleton containing just 1. But 0 is in the union, so 0 would
    have to equal 1 — contradiction."
    Hint (hidden := true) "Show 0 is in the union: `have h2 : (0 : N) ∈ ... := by left; rfl`. Then `have h3 := hpt h2`, use `change` to expose the equality as `(0 : N) = 1`, and close with `omega`."
    have h2 : (0 : ℕ) ∈ ({0} ∪ {1} : Set ℕ) := by left; rfl
    have h3 := hpt h2
    change (0 : ℕ) = 1 at h3
    omega

Conclusion "
You disproved the claim that powerset distributes over union!

**The counterexample**: `s = \\{0\\}`, `t = \\{1\\}`. The set
`\\{0, 1\\} = s ∪ t` is in `𝒫(s ∪ t)` (subset of itself) but not
in `𝒫 s ∪ 𝒫 t` (not a subset of either factor alone).

**Contrast with intersection**: `𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t` IS true
(Level 11) because a set that is a subset of both `s` and `t` is
automatically a subset of `s ∩ t`. But a subset of `s ∪ t` can draw
elements from BOTH `s` and `t`, without being contained in either one.

**Disproof strategy recap**:
1. `intro h` — assume the universal statement
2. Specialize to a concrete counterexample
3. Construct a witness that belongs to one side but not the other
4. Rewrite using the assumed equality to get a contradiction

This is the same disprove-by-counterexample pattern from Subset
World, now applied to a richer mathematical statement.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
