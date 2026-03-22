import Game.Metadata

World "FinsetImage"
Level 9

Title "Image of Intersection: The Easy Direction"

Introduction "
# Does Image Distribute Over Intersection?

You proved in Level 5 that image distributes over union:
$f(S \\cup T) = f(S) \\cup f(T)$. A natural question: does the
same hold for intersection?

$$f(S \\cap T) \\stackrel{?}{=} f(S) \\cap f(T)$$

The answer is **no** in general — but one direction always holds.

If $y \\in f(S \\cap T)$, then the witness $x$ is in BOTH $S$ and
$T$, so $f(x) \\in f(S)$ AND $f(x) \\in f(T)$. This gives:

$$f(S \\cap T) \\subseteq f(S) \\cap f(T)$$

The reverse can fail: $f(S)$ and $f(T)$ might share an output
value even when $S$ and $T$ don't share the input that produced it.
For example, if $f(2) = f(3) = 0$, $S = \\{2\\}$, $T = \\{3\\}$,
then $0 \\in f(S) \\cap f(T)$ but $S \\cap T = \\emptyset$.

**Your task**: Prove the easy direction.
"

/-- The image of an intersection is contained in the intersection of images. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f := by
  Hint "A subset goal unfolds to `∀ y, y ∈ lhs → y ∈ rhs`.
  Use `intro y hy` to introduce an element and its membership proof."
  intro y hy
  Hint "Now `hy : y ∈ (s ∩ t).image f`. Extract the witness with
  `rw [Finset.mem_image] at hy`, then `obtain`."
  rw [Finset.mem_image] at hy
  Hint "Use `obtain ⟨x, hx, hfx⟩ := hy` to extract the witness `x`,
  its membership `hx : x ∈ s ∩ t`, and `hfx : f x = y`."
  obtain ⟨x, hx, hfx⟩ := hy
  Hint "Now `hx : x ∈ s ∩ t`. Use `rw [Finset.mem_inter] at hx`
  to split into `x ∈ s ∧ x ∈ t`."
  rw [Finset.mem_inter] at hx
  Hint "Use `obtain ⟨hxs, hxt⟩ := hx` to get `hxs : x ∈ s` and
  `hxt : x ∈ t` separately."
  obtain ⟨hxs, hxt⟩ := hx
  Hint "The goal is `y ∈ s.image f ∩ t.image f`. Use
  `rw [Finset.mem_inter]` to convert to a conjunction, then
  `constructor` to split."
  rw [Finset.mem_inter]
  constructor
  · Hint "Prove `y ∈ s.image f` using `x ∈ s` as the witness.
    Try `rw [Finset.mem_image]` then `exact ⟨x, hxs, hfx⟩`."
    Hint (hidden := true) "Try `rw [Finset.mem_image]; exact ⟨x, hxs, hfx⟩`."
    rw [Finset.mem_image]
    exact ⟨x, hxs, hfx⟩
  · Hint "Prove `y ∈ t.image f` using `x ∈ t` as the witness.
    Try `rw [Finset.mem_image]` then `exact ⟨x, hxt, hfx⟩`."
    Hint (hidden := true) "Try `rw [Finset.mem_image]; exact ⟨x, hxt, hfx⟩`."
    rw [Finset.mem_image]
    exact ⟨x, hxt, hfx⟩

Conclusion "
You proved $f(S \\cap T) \\subseteq f(S) \\cap f(T)$.

The proof used the same extract-and-reuse pattern from Level 4:
1. Extract the witness from the hypothesis
2. Observe it satisfies BOTH membership conditions
3. Provide it as the witness for BOTH sides of the intersection

But unlike union, the **reverse** direction fails in general.
The counterexample: $f(2) = f(3) = 0$, $S = \\{2\\}$,
$T = \\{3\\}$. Then $0 \\in f(S) \\cap f(T)$ but
$S \\cap T = \\emptyset$, so $0 \\notin f(S \\cap T)$.

What goes wrong? When you extract witnesses from both sides
($a \\in S$ with $f(a) = y$ and $b \\in T$ with $f(b) = y$),
you get **two different witnesses** and can't conclude $a = b$
— unless $f$ is **injective**. You'll prove this repair later
in this world.

**Why union works but intersection doesn't**: Image is inherently
*surjective onto its own elements* — every $y \\in f(S)$ has a
preimage in $S$ by definition. Surjectivity gives the 'easy
direction' for free in both the union and intersection cases. The
question is always the 'hard direction': does every element of
$f(S) \\cap f(T)$ come from $S \\cap T$? For union, yes (always).
For intersection, only if $f$ is injective — because without
injectivity, different preimages can produce the same output.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_inter_subset Finset.image_inter Finset.image_inter_of_injOn Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right
