import Game.Metadata

World "FinsetImage"
Level 17

Title "Why Injectivity Matters"

Introduction "
# Counterexample: Intersection Without Injectivity

In Level 8 you proved the easy direction:
$f(S \\cap T) \\subseteq f(S) \\cap f(T)$. The introduction warned
that the reverse can fail. Now you'll see it happen.

Consider the **constant function** $f(n) = 0$ and the disjoint
singletons $S = \\{0\\}$, $T = \\{1\\}$.

- $f(S) = \\{0\\}$ and $f(T) = \\{0\\}$, so
  $f(S) \\cap f(T) = \\{0\\}$ — the output $0$ appears in both images.
- But $S \\cap T = \\emptyset$ (since $0 \\neq 1$), so
  $f(S \\cap T) = f(\\emptyset) = \\emptyset$.

The element $0$ is in $f(S) \\cap f(T)$ but NOT in $f(S \\cap T)$.
Why? Because the witnesses are **different**: $0 \\in S$ maps to $0$,
and $1 \\in T$ maps to $0$, but $0 \\neq 1$ so there's no single
witness in $S \\cap T$. If $f$ were **injective**, the witnesses
would have to be equal, closing the gap.

**Your task**: Prove both parts of this counterexample.
"

/-- The constant function shows image of intersection can be strictly smaller. -/
Statement :
    (0 : ℕ) ∈ ({0} : Finset ℕ).image (fun _ : ℕ => (0 : ℕ)) ∩
      ({1} : Finset ℕ).image (fun _ => 0) ∧
    (0 : ℕ) ∉ (({0} : Finset ℕ) ∩ {1}).image (fun _ => 0) := by
  Hint "Use `constructor` to split into the membership and non-membership parts."
  constructor
  -- Part 1: 0 ∈ image f {0} ∩ image f {1}
  · Hint "The goal is `0 ∈ image f left_set ∩ image f right_set`.
    Use `rw [Finset.mem_inter]` to split into both memberships,
    then `constructor`."
    rw [Finset.mem_inter]
    constructor
    · Hint "Prove `0 ∈ image (fun _ => 0) left_set`. The witness is `0`:
      it maps to `0`, and `0 ∈ left_set`.
      Try `rw [Finset.mem_image]; use 0`."
      rw [Finset.mem_image]
      Hint (hidden := true) "Try `use 0`."
      use 0
      Hint (hidden := true) "Use `constructor` then `rw [Finset.mem_singleton]`
      for membership, and `rfl` for the equation."
      constructor
      · rw [Finset.mem_singleton]
      · rfl
    · Hint "Prove `0 ∈ image (fun _ => 0) right_set`. The witness is `1`:
      it maps to `0`, and `1 ∈ right_set`.
      Try `rw [Finset.mem_image]; use 1`."
      rw [Finset.mem_image]
      Hint (hidden := true) "Try `use 1`."
      use 1
      Hint (hidden := true) "Use `constructor` then `rw [Finset.mem_singleton]`
      for membership, and `rfl` for the equation."
      constructor
      · rw [Finset.mem_singleton]
      · rfl
  -- Part 2: 0 ∉ image f ({0} ∩ {1})
  · Hint "For the non-membership part, use proof by contradiction:
    `intro h` assumes `0 ∈ image f (left_set ∩ right_set)`, and you
    must derive a contradiction."
    intro h
    Hint "Now `h` claims membership in the image. Extract the witness:
    `rw [Finset.mem_image] at h` then `obtain ⟨x, hx, _⟩ := h`."
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, _⟩ := h
    Hint "The witness `x` is supposedly in `left_set ∩ right_set`.
    Use `rw [Finset.mem_inter] at hx` to split."
    rw [Finset.mem_inter] at hx
    Hint "Use `obtain ⟨h0, h1⟩ := hx` to get `h0 : x ∈ left_set`
    and `h1 : x ∈ right_set`."
    obtain ⟨h0, h1⟩ := hx
    Hint "Now convert both to equations:
    `rw [Finset.mem_singleton] at h0 h1`
    This gives `h0 : x = 0` and `h1 : x = 1`.
    These contradict each other — `omega` closes it."
    Hint (hidden := true) "Try `rw [Finset.mem_singleton] at h0 h1; omega`."
    rw [Finset.mem_singleton] at h0 h1
    omega

Conclusion "
You just witnessed the failure: $0 \\in f(S) \\cap f(T)$ but
$0 \\notin f(S \\cap T)$, because the constant function maps
*different* inputs to the same output.

The key insight: when you extract witnesses from both images,
you get $a \\in S$ with $f(a) = 0$ and $b \\in T$ with $f(b) = 0$.
To place the witness in $S \\cap T$, you need $a = b$ — which
requires **injectivity**.

In the next level, you'll prove that injectivity repairs this
gap, giving the full distributivity:
$f \\text{ injective} \\implies f(S \\cap T) = f(S) \\cap f(T)$.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_inter Finset.image_inter_of_injOn Finset.image_inter_subset
