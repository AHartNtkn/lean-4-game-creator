import Game.Metadata

World "PsetFinset"
Level 14

Title "Boss: Image Preserves Set Difference"

Introduction "
# Boss: Image and Set Difference Under Injectivity

Given an **injective** function $f$, prove:

$$(s \\setminus t).\\text{image}\\; f \\;\\subseteq\\; s.\\text{image}\\; f \\;\\setminus\\; t.\\text{image}\\; f$$

If you remove elements of $t$ from $s$ *before* applying $f$,
the result is contained in what you'd get by applying $f$ to $s$
and then removing the image of $t$.

This proof integrates 7+ moves from FinsetOperations and FinsetImage.
No new moves — only moves you've already used.
"

/-- Under injectivity, image preserves set difference (as a subset). -/
Statement (f : ℕ → ℕ) (hf : Function.Injective f) (s t : Finset ℕ) :
    (s \ t).image f ⊆ s.image f \ t.image f := by
  rw [Finset.subset_iff]
  intro y hy
  Hint "Extract the witness from `hy`, unfold the source sdiff,
  then build both parts of the target sdiff."
  rw [Finset.mem_image] at hy
  obtain ⟨a, ha, hfa⟩ := hy
  rw [Finset.mem_sdiff] at ha
  rw [Finset.mem_sdiff]
  constructor
  -- Part 1: y ∈ s.image f
  · Hint (hidden := true) "`rw [Finset.mem_image]; use a; constructor; exact ha.1; exact hfa`"
    rw [Finset.mem_image]
    exact ⟨a, ha.1, hfa⟩
  -- Part 2: y ∉ t.image f
  · Hint "The goal is `y ∉ t.image f`. Assume `y ∈ t.image f`,
    extract a witness `b ∈ t`, and use injectivity to derive `a = b`."
    Hint (hidden := true) "`intro hyt`, then
    `rw [Finset.mem_image] at hyt; obtain ⟨b, hbt, hfb⟩ := hyt`."
    intro hyt
    rw [Finset.mem_image] at hyt
    obtain ⟨b, hbt, hfb⟩ := hyt
    Hint "You need `f a = f b` to apply injectivity. You have
    `hfa : f a = y` and `hfb : f b = y` — both sides equal `y`.
    Use `rw` with both hypotheses to build the equality."
    Hint (hidden := true) "`have hfab : f a = f b := by rw [hfa, hfb]`.
    Then `have hab : a = b := hf hfab`.
    `rw [hab] at ha; exact ha.2 hbt`."
    have hfab : f a = f b := by rw [hfa, hfb]
    have hab : a = b := hf hfab
    rw [hab] at ha
    exact ha.2 hbt

Conclusion "
Congratulations — you've completed the **Finset Problem Set**!

You proved that injective functions preserve set difference:
$f(s \\setminus t) \\subseteq f(s) \\setminus f(t)$ when $f$ is injective.

The key insight: injectivity was essential. Without it, two
different elements $a \\notin t$ and $b \\in t$ could map to
the same $y$, making $y$ appear in $t.\\text{image}\\; f$ even though
it came from an element outside $t$. Injectivity forces $a = b$,
which creates the contradiction.

**Equality, not just subset**: You proved the $\\subseteq$ direction.
Under injectivity, the reverse inclusion also holds:
$f(s) \\setminus f(t) \\subseteq f(s \\setminus t)$. Together they
give **equality**: $f(s \\setminus t) = f(s) \\setminus f(t)$ when
$f$ is injective. This is `Finset.image_sdiff` in Mathlib.
Injectivity fully 'repairs' the interaction between image and
set difference — just as it repairs intersection
(`Finset.image_inter_of_injOn` from FinsetImage L17).

**What's next**: The next world introduces **cardinality** —
the number of elements in a finset — and the fundamental
counting identities.
"

/-- `Finset.image_sdiff s t hf` states that when `f` is injective,
`(s \\ t).image f = s.image f \\ t.image f` — image distributes
over set difference under injectivity. -/
TheoremDoc Finset.image_sdiff as "Finset.image_sdiff" in "Finset"

/-- `Finset.image_sdiff_of_injOn` is the `InjOn` variant of
`Finset.image_sdiff` — requires injectivity only on the relevant sets. -/
TheoremDoc Finset.image_sdiff_of_injOn as "Finset.image_sdiff_of_injOn" in "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right Finset.image_inter Finset.image_inter_of_injOn Finset.image_inter_subset sdiff_sdiff_right_self Finset.image_sdiff Finset.image_sdiff_of_injOn
