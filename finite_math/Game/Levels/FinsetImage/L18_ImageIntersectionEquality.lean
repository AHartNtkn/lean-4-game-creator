import Game.Metadata

World "FinsetImage"
Level 18

Title "Intersection Repaired: Injectivity Gives Equality"

Introduction "
# The Repair: Injectivity Makes Intersection Distribute

In Level 8, you proved $f(S \\cap T) \\subseteq f(S) \\cap f(T)$
and saw that the reverse fails when $f$ collapses distinct inputs
to the same output.

Now you have the tool to fix this: **injectivity**. If $f$ is
injective, then the two witnesses extracted from $f(S)$ and $f(T)$
must be equal, so their shared preimage is in $S \\cap T$.

**Your task**: Given `hf : Function.Injective f`, prove the
reverse containment:

$$f(S) \\cap f(T) \\subseteq f(S \\cap T)$$

Strategy:
1. Take $y \\in f(S) \\cap f(T)$
2. Extract witnesses: $a \\in S$ with $f(a) = y$ and $b \\in T$
   with $f(b) = y$
3. Derive $f(a) = f(b)$ from $f(a) = y = f(b)$
4. Apply injectivity to get $a = b$
5. Now $a \\in S \\cap T$, so $y \\in f(S \\cap T)$
"

/-- Under injectivity, the intersection of images is contained in the image of intersection. -/
Statement (f : ℕ → ℕ) (hf : Function.Injective f) (s t : Finset ℕ) :
    s.image f ∩ t.image f ⊆ (s ∩ t).image f := by
  Hint "Subset goal: use `intro y hy` to introduce the element."
  intro y hy
  Hint "Now `hy : y ∈ s.image f ∩ t.image f`. Use
  `rw [Finset.mem_inter] at hy` to split into both memberships."
  rw [Finset.mem_inter] at hy
  Hint "Use `obtain ⟨hys, hyt⟩ := hy` to get `hys : y ∈ s.image f`
  and `hyt : y ∈ t.image f`."
  obtain ⟨hys, hyt⟩ := hy
  Hint "Extract witnesses from both sides. Start with
  `rw [Finset.mem_image] at hys` then `obtain ⟨a, has, hfa⟩ := hys`."
  rw [Finset.mem_image] at hys
  obtain ⟨a, has, hfa⟩ := hys
  Hint "Now extract from the other side: `rw [Finset.mem_image] at hyt`
  then `obtain ⟨b, hbt, hfb⟩ := hyt`."
  rw [Finset.mem_image] at hyt
  obtain ⟨b, hbt, hfb⟩ := hyt
  Hint "You have `hfa : f a = y` and `hfb : f b = y`. Both equal
  `y`, so `f a = f b`. Derive this in two steps:

  Step 1 — prove `f a = f b`:
  `have hfab : f a = f b := by rw [hfa, hfb]`

  Step 2 — apply injectivity:
  `have hab : a = b := hf hfab`"
  Hint (hidden := true) "One-liner alternative:
  `have hab : a = b := hf (by rw [hfa, hfb])`"
  have hfab : f a = f b := by rw [hfa, hfb]
  Hint (hidden := true) "Now apply injectivity:
  `have hab : a = b := hf hfab`"
  have hab : a = b := hf hfab
  Hint "Now `hab : a = b`. The witness for the goal is `a`, which
  is in `s ∩ t` (since `a ∈ s` from `has` and `a = b ∈ t` from
  `hab` and `hbt`).

  Use `rw [Finset.mem_image]` to convert the goal."
  rw [Finset.mem_image]
  Hint "Provide the witness: `use a`. Then you need `a ∈ s ∩ t`
  and `f a = y`."
  use a
  Hint "Use `constructor` to split. For the intersection part,
  use `rw [Finset.mem_inter]; exact ⟨has, hab ▸ hbt⟩`.
  For the equation, use `exact hfa`."
  Hint (hidden := true) "Try `constructor` then:
  - `rw [Finset.mem_inter]; constructor; exact has; rw [hab]; exact hbt`
  - `exact hfa`"
  constructor
  · rw [Finset.mem_inter]
    constructor
    · exact has
    · rw [hab]; exact hbt
  · exact hfa

Conclusion "
You proved the **repair**: when $f$ is injective,

$$f(S) \\cap f(T) \\subseteq f(S \\cap T)$$

Combined with Level 8 ($f(S \\cap T) \\subseteq f(S) \\cap f(T)$,
which holds for all $f$), this gives the full distributivity:

$$f \\text{ injective} \\implies f(S \\cap T) = f(S) \\cap f(T)$$

Compare with union, where distributivity is free (no injectivity
needed). This asymmetry is a fundamental theme:

| Operation | Distributes? | Condition |
|---|---|---|
| Union | Always | None |
| Intersection | Conditionally | $f$ injective |

The key proof move was deriving $a = b$ from $f(a) = f(b)$
using injectivity — the same move from Level 14, now applied in
a membership context rather than a cardinality context. This shows
that injectivity is a general-purpose tool, not just a cardinality
trick.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_inter Finset.image_inter_of_injOn Finset.image_inter_subset Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right
