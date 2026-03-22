import Game.Metadata

World "PsetFinset"
Level 7

Title "Injective Non-Membership"

Introduction "
# Injectivity Preserves Non-Membership

If $f$ is injective and $a \\notin s$, then $f(a) \\notin f(s)$.

Intuitively: if $a$ isn't in the original set, its image can't
appear in the image set (because no other element maps to $f(a)$
when $f$ is injective).

The proof uses backward image extraction and injectivity to derive
a contradiction.
"

/-- Injective functions preserve non-membership. -/
Statement (f : ℕ → ℕ) (hf : Function.Injective f) (s : Finset ℕ)
    (a : ℕ) (hna : a ∉ s) : f a ∉ s.image f := by
  Hint "The goal is `f a ∉ s.image f`, which is a negation.
  Use `intro hfa` to assume `f a ∈ s.image f` and derive `False`."
  intro hfa
  Hint (hidden := true) "Extract the witness: `rw [Finset.mem_image] at hfa`
  then `obtain ⟨b, hbs, hfb⟩ := hfa`. Apply injectivity:
  `have hab : b = a := hf hfb`. Rewrite and contradict:
  `rw [hab] at hbs; exact hna hbs`."
  rw [Finset.mem_image] at hfa
  obtain ⟨b, hbs, hfb⟩ := hfa
  have hab : b = a := hf hfb
  rw [hab] at hbs
  exact hna hbs

Conclusion "
The proof pattern:
1. Assume $f(a) \\in f(s)$ — extract a witness $b \\in s$ with $f(b) = f(a)$
2. Apply injectivity: $f(b) = f(a) \\implies b = a$
3. Rewrite: $b \\in s$ becomes $a \\in s$, contradicting $a \\notin s$

This is a different use of injectivity from cardinality preservation —
here injectivity creates a contradiction rather than establishing
a count.
"

/-- `Finset.not_mem_image_of_injective` states that if `f` is injective
and `a ∉ s`, then `f a ∉ s.image f`. -/
TheoremDoc Finset.not_mem_image_of_injective as "Finset.not_mem_image_of_injective" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.not_mem_image_of_injective
