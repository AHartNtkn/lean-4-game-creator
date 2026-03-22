import Game.Metadata

World "FinsetImage"
Level 2

Title "Choosing the Right Witness"

Introduction "
# A Different Kind of Finset

In Level 1, the finset was `Finset.range n` and membership used
`Finset.mem_range`. But finsets can also be built from explicit
elements using `{a, b, c}` notation (which desugars to `insert`
and `singleton`).

**Your task**: Prove that $25 \\in \\text{image}(n \\mapsto n^2,\\; \\{2, 5, 8\\})$.

The preimage of $25$ under $n \\mapsto n^2$ is $5$, since $5^2 = 25$.
And $5 \\in \\{2, 5, 8\\}$ because it's an explicit member.

The proof starts the same (`rw [Finset.mem_image]; use 5`), but the
membership subgoal uses `Finset.mem_insert` and `Finset.mem_singleton`
instead of `Finset.mem_range`.
"

/-- 25 is in the image of (n ↦ n ^ 2) applied to {2, 5, 8}. -/
Statement : (25 : ℕ) ∈ ({2, 5, 8} : Finset ℕ).image (fun n => n ^ 2) := by
  Hint "Same first step: `rw [Finset.mem_image]` to convert to an existential."
  rw [Finset.mem_image]
  Hint "Solve: $n^2 = 25$ gives $n = 5$. Try `use 5`."
  Hint (hidden := true) "Try `use 5`."
  use 5
  Hint "After `use 5`, two subgoals remain:
  1. `5 ∈ the finset` (membership)
  2. `5 ^ 2 = 25` (the functional equation)

  Use `constructor` to split them."
  constructor
  · Hint "The goal is membership in an insert-based finset.
    For these finsets, the membership lemma is:
    `Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s`

    Try `rw [Finset.mem_insert]` to start peeling off elements."
    Hint "If you want to skip the step-by-step, the full membership
    chain is: `rw [Finset.mem_insert]; right; rw [Finset.mem_insert]; left; rfl`."
    rw [Finset.mem_insert]
    Hint "The goal is a disjunction: `5 = 2 ∨ ...`. Since 5 is not 2,
    use `right` to take the second disjunct."
    right
    Hint "Now the goal is membership in a smaller finset.
    Rewrite again: `rw [Finset.mem_insert]`."
    rw [Finset.mem_insert]
    Hint "The goal is `5 = 5 ∨ ...`. Use `left` since `5 = 5`."
    left
    rfl
  · Hint (hidden := true) "The equation `5 ^ 2 = 25` is verified by `rfl`."
    rfl

Conclusion "
The image membership recipe works with ANY finset — not just ranges.
The only difference is step 3: how you prove `x ∈ s`.

- **Range finsets** (`Finset.range n`): use `Finset.mem_range`
- **Insert-based finsets** (explicit elements): use `Finset.mem_insert`
  to peel off elements one at a time, then `Finset.mem_singleton` at the end

The witness-finding step is the same: solve $f(x) = y$ for $x$.
The membership proof adapts to the finset representation.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
