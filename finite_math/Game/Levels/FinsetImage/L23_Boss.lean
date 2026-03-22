import Game.Metadata

World "FinsetImage"
Level 23

Title "Boss: Image Membership, Bounds, and Injectivity"

Introduction "
# Boss: Putting It All Together

Consider $f(n) = n + 3$ applied to $S = \\{0, 1, \\ldots, 9\\}$.
This level integrates three core move families from the world.

**Part 1** — Forward membership (Levels 1-2):
Prove $12 \\in f(S)$ by providing the witness $9$.

**Part 2** — Subset bound via backward extraction (Levels 3-8):
Prove $f(S) \\subseteq \\{0, \\ldots, 12\\}$. Every element
$n + 3$ where $n < 10$ satisfies $n + 3 < 13$.

**Part 3** — Cardinality upper bound (Level 12):
The image can only shrink: $|f(S)| \\leq |S|$.

**Part 4** — Exact cardinality via injectivity (Levels 13-14):
Prove $|f(S)| = |S|$ by proving that $n \\mapsto n+3$ is injective.

No new moves — only moves seeded in Levels 1-21.
"

/-- Forward membership, subset bound, cardinality bounds, and injectivity. -/
Statement :
    (12 : ℕ) ∈ (Finset.range 10).image (fun n => n + 3) ∧
    (Finset.range 10).image (fun n => n + 3) ⊆ Finset.range 13 ∧
    ((Finset.range 10).image (fun n => n + 3)).card ≤
      (Finset.range 10).card ∧
    ((Finset.range 10).image (fun n => n + 3)).card =
      (Finset.range 10).card := by
  Hint "Use `constructor` to split into Part 1 and the remaining parts."
  constructor
  -- Part 1: 12 ∈ image (· + 3) (range 10)
  · Hint "Forward membership: `rw [Finset.mem_image]`, provide the witness.
    Solve: $n + 3 = 12$ gives $n = 9$."
    rw [Finset.mem_image]
    Hint (hidden := true) "Try `use 9`."
    use 9
    Hint "Lean verified `9 + 3 = 12`. Remaining: `9 ∈ Finset.range 10`.
    Use `rw [Finset.mem_range]; omega`."
    rw [Finset.mem_range]
    omega
  constructor
  -- Part 2: image (· + 3) (range 10) ⊆ range 13
  · Hint "Subset goal: introduce an element with `intro x hx`,
    then extract the witness from `hx` and show `x < 13`."
    intro x hx
    Hint "Use backward extraction: `rw [Finset.mem_image] at hx`
    then `obtain ⟨a, ha, hfa⟩ := hx`."
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, hfa⟩ := hx
    Hint "You have `ha : a ∈ Finset.range 10` and
    `hfa : a + 3 = x`. Rewrite `ha` to get the bound:
    `rw [Finset.mem_range] at ha` gives `a < 10`.
    Then `rw [Finset.mem_range]` on the goal gives `x < 13`.
    Finally `omega` closes it."
    Hint (hidden := true) "Try:
    `rw [Finset.mem_range] at ha`
    `rw [Finset.mem_range]`
    `omega`"
    rw [Finset.mem_range] at ha
    rw [Finset.mem_range]
    omega
  constructor
  -- Part 3: card upper bound
  · Hint "The image can only shrink: `Finset.card_image_le` says
    $|f(S)| \\leq |S|$ for any function. Apply it directly."
    Hint (hidden := true) "Try `exact Finset.card_image_le`."
    exact Finset.card_image_le
  -- Part 4: card preserved
  · Hint "Now prove the exact count. Apply
    `Finset.card_image_of_injective` — this leaves the
    injectivity goal."
    apply Finset.card_image_of_injective
    Hint "Prove `Function.Injective (fun n => n + 3)`.
    Use `show ∀ a b : ℕ, a + 3 = b + 3 → a = b` to restate
    with the function applied, then `intro a b h; omega`."
    show ∀ a b : ℕ, a + 3 = b + 3 → a = b
    intro a b h
    omega

Conclusion "
Congratulations — you've completed **Finset Image**!

You mastered four core move families:

**1. Forward membership** (witness construction):
- `rw [Finset.mem_image]; use x; constructor`
- Choose `x` by solving `f(x) = y`

**2. Backward extraction** (witness destruction):
- `rw [Finset.mem_image] at h; obtain ⟨x, hx, hfx⟩ := h`
- Used for non-membership proofs, subset proofs, and re-use

**3. Cardinality bounds**:
- `Finset.card_image_le`: $|f(S)| \\leq |S|$ (always)
- `Finset.card_image_of_injective`: $|f(S)| = |S|$ (when $f$ is injective)
- `Finset.card_image_iff`: $|f(S)| = |S| \\iff f$ is injective on $S$
- Injectivity proof: `intro a b h; omega`

**4. Image algebra**:
- Image distributes over union: $f(S \\cup T) = f(S) \\cup f(T)$
- Image of intersection: $f(S \\cap T) \\subseteq f(S) \\cap f(T)$
  (equality under injectivity)
- Image of singleton: $f(\\{a\\}) = \\{f(a)\\}$

| Theorem | What it says |
|---|---|
| `Finset.mem_image` | `y ∈ s.image f ↔ ∃ x ∈ s, f x = y` |
| `Finset.card_image_le` | `(s.image f).card ≤ s.card` |
| `Finset.card_image_of_injective` | injective `f` implies `(s.image f).card = s.card` |
| `Finset.card_image_iff` | `(s.image f).card = s.card ↔ Set.InjOn f ↑s` |

**Injectivity vs. surjectivity**: This world focused on
*injectivity* — does $f$ preserve distinctness? The dual question
is *surjectivity* — does $f$ cover the target? When does
$s.\\text{image}\\; f = t$ for a target set $t$? Cardinality will
connect the two: counting arguments show that injectivity between
same-size sets *implies* surjectivity. The pigeonhole principle is
a non-surjectivity result in disguise.

**The dual operation**: Everything in this world went forward —
given a source set $S$, compute $f(S)$. The dual question goes
backward: given a target set $T$, which elements of the domain
map *into* $T$? That's `Finset.preimage` — the finset version of
the preimage. It appears in later worlds when you need to reason
about which inputs produce a desired output.

**What's next**: Problem Set Finset will test these skills on fresh
problems without scaffolding.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right Finset.image_inter Finset.image_inter_of_injOn Finset.image_inter_subset
