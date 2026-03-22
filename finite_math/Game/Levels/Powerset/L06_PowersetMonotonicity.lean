import Game.Metadata

World "Powerset"
Level 6

Title "Powerset Monotonicity"

Introduction "
# Bigger Set, Bigger Powerset

If `s ⊆ t`, then every subset of `s` is also a subset of `t`.
This means `s.powerset ⊆ t.powerset` — the powerset operation
is **monotone**.

**Your task**: Prove that `s.powerset ⊆ t.powerset` given `h : s ⊆ t`.

The statement `s.powerset ⊆ t.powerset` means: for every finset `u`,
if `u ∈ s.powerset` then `u ∈ t.powerset`. So you'll need to:
1. Introduce `u` and the hypothesis `u ∈ s.powerset`
2. Use `mem_powerset` to convert both sides to subset claims
3. Prove `u ⊆ t` from `u ⊆ s` and `s ⊆ t` by chaining

**New syntax**: You can rewrite in multiple places at once using
`rw [...] at hu ⊢`, where `⊢` refers to the goal. This rewrites
both the hypothesis `hu` and the goal in one step.
"

/-- If s ⊆ t, then s.powerset ⊆ t.powerset. -/
Statement (s t : Finset ℕ) (h : s ⊆ t) : s.powerset ⊆ t.powerset := by
  Hint "The goal `s.powerset ⊆ t.powerset` means:
  for all `u`, if `u ∈ s.powerset` then `u ∈ t.powerset`.
  Start by introducing the element and its membership hypothesis."
  Hint (hidden := true) "Try `intro u hu`."
  intro u hu
  Hint "Now you have `hu : u ∈ s.powerset` and need `u ∈ t.powerset`.
  Use `rw [Finset.mem_powerset] at hu ⊢` to convert both the
  hypothesis and the goal to subset claims. The `⊢` symbol refers
  to the goal."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at hu ⊢`."
  rw [Finset.mem_powerset] at hu ⊢
  Hint "Now `hu : u ⊆ s` and the goal is `u ⊆ t`. Since `⊆` means
  'every element of the left is in the right', introduce an element
  `x` and its membership proof `hx : x ∈ u`."
  Hint (hidden := true) "Try `intro x hx`."
  intro x hx
  Hint "You need `x ∈ t`. You know `hx : x ∈ u` and `hu : u ⊆ s`,
  so `hu hx : x ∈ s`. Then `h : s ⊆ t`, so `h (hu hx) : x ∈ t`."
  Hint (hidden := true) "Try `exact h (hu hx)`."
  exact h (hu hx)

Conclusion "
You proved powerset monotonicity: if $s \\subseteq t$, then
$\\mathcal{P}(s) \\subseteq \\mathcal{P}(t)$.

**Proof recipe**:
1. `intro u hu` — introduce the element and membership
2. `rw [mem_powerset] at hu ⊢` — convert both to subset claims
3. `intro x hx` — introduce an element of `u`
4. `exact h (hu hx)` — chain: `x ∈ u → x ∈ s → x ∈ t`

**The key move**: Step 4 chains two subset hypotheses by function
application. Since `u ⊆ s` means `∀ x ∈ u, x ∈ s`, applying
`hu` to `hx` gives `x ∈ s`, and then `h` gives `x ∈ t`.

**The simultaneous-rewrite pattern**: Step 2 used `rw [...] at hu ⊢`
to rewrite in *both* a hypothesis and the goal in one command. The
`⊢` symbol refers to the goal. This pattern is useful whenever you
need to normalize related expressions in different locations. You
will use it again in Level 8 and in the boss.

**Library connection**: Mathlib calls this `Finset.powerset_mono` —
you just proved a real library theorem from first principles!
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
