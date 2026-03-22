import Game.Metadata

World "FinsetImage"
Level 11

Title "Every Output is the Constant"

Introduction "
# When Image Shrinks: A Constant Function

So far every image preserved cardinality — injective functions
map distinct inputs to distinct outputs. But what happens when a
function is NOT injective?

The simplest example: the constant function $n \\mapsto 0$ maps
every element to $0$. Applied to $\\{1, 2, 3\\}$, the image is
$\\{0\\}$ — three elements collapsed to one.

Before proving the full equality $f(\\{1,2,3\\}) = \\{0\\}$ (next
level after), let's first prove the forward containment: every
element of the image must equal $0$.

**Your task**: Prove that the image of $\\{1, 2, 3\\}$ under the
constant function $n \\mapsto 0$ is contained in $\\{0\\}$.

This uses the backward extraction move from Level 3: extract the
witness, observe the function maps it to $0$.
"

/-- The image of {1,2,3} under the constant function is contained in {0}. -/
Statement : ({1, 2, 3} : Finset ℕ).image (fun _ => (0 : ℕ)) ⊆ {0} := by
  Hint "A subset goal `s ⊆ t` unfolds to `∀ x, x ∈ s → x ∈ t`.
  Use `intro x hx` to introduce an arbitrary element and its
  membership proof."
  intro x hx
  Hint "Now `hx : x ∈ image (fun _ => 0) ...`. Extract the witness
  with `rw [Finset.mem_image] at hx`."
  rw [Finset.mem_image] at hx
  Hint "Use `obtain ⟨a, _, ha⟩ := hx` to extract the witness.
  We don't need the membership proof (hence `_`)."
  obtain ⟨a, _, ha⟩ := hx
  Hint "You have `ha : 0 = x` (since the function maps everything to 0).
  The goal is `x ∈ singleton 0`. Use `rw [Finset.mem_singleton]`
  to convert to `x = 0`, then close with `omega`."
  Hint (hidden := true) "Try `rw [Finset.mem_singleton]; omega`."
  rw [Finset.mem_singleton]
  omega

Conclusion "
This is the **forward containment** for a constant function's image:
every element of $f(S)$ must equal the constant value.

The proof used backward extraction: given `x ∈ image (fun _ => 0) s`,
the witness `a ∈ s` satisfies `0 = x`, so `x = 0`.

Key insight: the constant function $n \\mapsto 0$ maps $\\{1, 2, 3\\}$
(3 elements) to $\\{0\\}$ (1 element). This is the most extreme case
of non-injective shrinkage: ALL elements collapse to one point.

But is $\\{0\\}$ contained in the image? That's the reverse direction
— you'll prove the full equality soon.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_const Finset.image_singleton Finset.image_eq_empty
