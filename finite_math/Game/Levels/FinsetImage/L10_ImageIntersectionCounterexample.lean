import Game.Metadata

World "FinsetImage"
Level 10

Title "Why Injectivity Matters: A Concrete Failure"

Introduction "
# Seeing the Failure Without Injectivity

In Level 9, you proved that $f(S \\cap T) \\subseteq f(S) \\cap f(T)$
always holds. The reverse direction can fail when $f$ is not injective.
You saw the counterexample in the conclusion — now you'll **prove** it.

Take $f(x) = 0$ (the constant function), $S = \\{1\\}$, $T = \\{2\\}$.

- $S \\cap T = \\emptyset$, so $f(S \\cap T) = f(\\emptyset) = \\emptyset$
- But $f(S) = \\{0\\}$ and $f(T) = \\{0\\}$, so $f(S) \\cap f(T) = \\{0\\}$

The intersection of the images is non-empty, but the image of the
intersection is empty. The function $f$ creates a 'phantom' intersection
element: $0$ appears in both images but comes from different sources
($1 \\in S$ and $2 \\in T$), not from a shared source in $S \\cap T$.

**Your task**: Prove that $0 \\in f(S) \\cap f(T)$ but $0 \\notin f(S \\cap T)$.
This witnesses the strict containment $f(S \\cap T) \\subsetneq f(S) \\cap f(T)$.
"

/-- A concrete witness that image of intersection ⊊ intersection of images
when f is not injective. -/
Statement : (0 : ℕ) ∈ ({1} : Finset ℕ).image (fun _ => (0 : ℕ)) ∩
              ({2} : Finset ℕ).image (fun _ => (0 : ℕ)) ∧
            (0 : ℕ) ∉ (({1} : Finset ℕ) ∩ {2}).image (fun _ => (0 : ℕ)) := by
  Hint "Split the conjunction with `constructor`."
  constructor
  -- Part 1: 0 ∈ f({1}) ∩ f({2})
  · Hint "The goal is `0 ∈ image(...) ∩ image(...)`. Rewrite with
    `Finset.mem_inter` to split into two membership goals."
    rw [Finset.mem_inter]
    Hint "Use `constructor` to split the conjunction."
    constructor
    · Hint "Prove `0 ∈ image (fun _ => 0) singleton 1`. Use
      `rw [Finset.mem_image]` then provide the witness."
      Hint (hidden := true) "`rw [Finset.mem_image]; use 1; constructor;
      · rw [Finset.mem_singleton]
      · rfl`"
      rw [Finset.mem_image]
      exact ⟨1, Finset.mem_singleton.mpr rfl, rfl⟩
    · Hint (hidden := true) "`rw [Finset.mem_image]; use 2; constructor;
      · rw [Finset.mem_singleton]
      · rfl`"
      rw [Finset.mem_image]
      exact ⟨2, Finset.mem_singleton.mpr rfl, rfl⟩
  -- Part 2: 0 ∉ f({1} ∩ {2})
  · Hint "The goal is `0 ∉ image (fun _ => 0) (singleton 1 ∩ singleton 2)`.
    Use `intro h` and `rw [Finset.mem_image] at h` to extract a witness."
    intro h
    Hint (hidden := true) "`rw [Finset.mem_image] at h` then
    `obtain ⟨x, hx, _⟩ := h` and `rw [Finset.mem_inter] at hx`.
    The witness `x` must be in both `singleton 1` and `singleton 2`,
    which is impossible."
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, _⟩ := h
    rw [Finset.mem_inter] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [Finset.mem_singleton] at h1 h2
    omega

Conclusion "
You've proved that the containment $f(S \\cap T) \\subseteq f(S) \\cap f(T)$
can be **strict** when $f$ is not injective.

**The phantom witness phenomenon**: The element $0$ in
$f(\\{1\\}) \\cap f(\\{2\\})$ is a **phantom** — it looks like it belongs to
the image of the intersection, but it doesn't. Why? Because the
witnesses that produce it are *different*: $1 \\in \\{1\\}$ maps to $0$,
and $2 \\in \\{2\\}$ maps to $0$, but $1 \\neq 2$, so there's no single
element in $\\{1\\} \\cap \\{2\\}$ that maps to $0$.

**Why union works but intersection doesn't**: Compare the two results:

- $f(S \\cup T) = f(S) \\cup f(T)$ — **exact equality**, always.
- $f(S \\cap T) \\subseteq f(S) \\cap f(T)$ — **only containment** in general.

For union, if $y \\in f(S) \\cup f(T)$, the witness $x$ that maps to $y$
is in $S$ or $T$, so it's in $S \\cup T$. No phantom is possible — the
single witness suffices.

For intersection, $y \\in f(S) \\cap f(T)$ gives you **two** witnesses:
$a \\in S$ and $b \\in T$ with $f(a) = f(b) = y$. Unless $a = b$ (which
injectivity guarantees), these witnesses are useless for proving
$y \\in f(S \\cap T)$.

The structural reason: image is 'surjective onto its own elements' —
every element of $f(S)$ has a preimage by definition. Union only needs
*existence* of a preimage (one witness anywhere), which image always
provides. Intersection needs a *shared* preimage (one witness in both
sets), which image can't guarantee without injectivity.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_inter_subset Finset.image_inter Finset.image_inter_of_injOn Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.inter_subset_left Finset.inter_subset_right inf_le_left inf_le_right Finset.image_const Finset.image_singleton
