import Game.Metadata

World "FinsetImage"
Level 12

Title "A Partially Non-Injective Function"

Introduction "
# Between Injective and Constant

The constant function $n \\mapsto 0$ collapses everything to a single
point. But most non-injective functions are less extreme — they
collapse SOME inputs while keeping others distinct.

Consider $n \\mapsto n - 1$ on $\\{0, 1, 2, 3\\}$:
- $0 \\mapsto 0$ (truncated subtraction: $0 - 1 = 0$ in $\\mathbb{N}$)
- $1 \\mapsto 0$ (collision with $0$!)
- $2 \\mapsto 1$
- $3 \\mapsto 2$

The image is $\\{0, 1, 2\\}$ — three elements instead of four.
Not a total collapse like the constant function, but a partial one:
$0$ and $1$ collide while $2$ and $3$ map to distinct values.

**Your task**: Prove two things about this function:
1. $1 \\in \\text{image}(n \\mapsto n-1,\\; \\text{range}(4))$
   (the image is not empty — $2$ maps to $1$)
2. $3 \\notin \\text{image}(n \\mapsto n-1,\\; \\text{range}(4))$
   (the element $3$ is lost — $n - 1 = 3$ requires $n = 4$,
   but $4 \\notin \\text{range}(4)$)
"

/-- The image of range 4 under (n ↦ n - 1) contains 1 but not 3. -/
Statement : (1 : ℕ) ∈ (Finset.range 4).image (fun n => n - 1) ∧
    (3 : ℕ) ∉ (Finset.range 4).image (fun n => n - 1) := by
  Hint "Use `constructor` to split into the two parts."
  constructor
  -- Part 1: 1 ∈ image
  · Hint "Forward membership: `rw [Finset.mem_image]`, then provide
    the witness. Which `n ∈ range 4` satisfies `n - 1 = 1`?
    Answer: `n = 2`."
    rw [Finset.mem_image]
    Hint (hidden := true) "Try `use 2`."
    use 2
    Hint (hidden := true) "Use `rw [Finset.mem_range]; omega` or `constructor` then close each part."
    rw [Finset.mem_range]
    omega
  -- Part 2: 3 ∉ image
  · Hint "Non-membership: assume `3` is in the image with `intro h`,
    then extract the witness and derive a contradiction."
    intro h
    Hint "Use `rw [Finset.mem_image] at h` then
    `obtain ⟨x, hx, hfx⟩ := h`."
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hfx⟩ := h
    Hint "You have `hx : x ∈ Finset.range 4` (i.e., `x < 4`)
    and `hfx : x - 1 = 3`. In natural numbers, `x - 1 = 3`
    forces `x = 4`, but `x < 4`. Contradiction!

    Use `rw [Finset.mem_range] at hx` then `omega`."
    rw [Finset.mem_range] at hx
    omega

Conclusion "
This function $n \\mapsto n - 1$ on $\\{0,1,2,3\\}$ shows **partial
non-injectivity**: $0$ and $1$ both map to $0$ (a collision), while
$2 \\mapsto 1$ and $3 \\mapsto 2$ are distinct.

The image is $\\{0, 1, 2\\}$ — cardinality 3, down from 4. The
shrinkage is proportional to the number of collisions:
- Constant function: all collide → card drops to 1
- This function: one collision → card drops by 1
- Injective function: no collisions → card preserved

This spectrum is the content of `Finset.card_image_le`: the image
can only shrink, and it shrinks by exactly the number of collisions.
The next levels formalize this with cardinality.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
