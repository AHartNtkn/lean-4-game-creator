import Game.Metadata

World "FinsetImage"
Level 1

Title "First Contact with Image"

Introduction "
# Finset.image: Applying a Function to Every Element

Given a function `f : α → β` and a finset `s : Finset α`, the **image**
`s.image f` (or `Finset.image f s`) is the finset of all values `f x`
for `x ∈ s`. This is the formal version of the set-theoretic image
$f(S) = \\{f(x) \\mid x \\in S\\}$.

The key membership characterization is `Finset.mem_image`:
```
Finset.mem_image : y ∈ s.image f ↔ ∃ x ∈ s, f x = y
```

To prove `y ∈ s.image f`, the proof recipe is:
1. `rw [Finset.mem_image]` — converts membership to an existential
2. `use x` — provide the witness (the preimage of `y`)
3. Prove that `x ∈ s` and `f x = y`

**Your task**: Prove that $3 \\in \\text{image}(n \\mapsto n+1,\\; \\{0,1,2,3\\})$.

The preimage of $3$ under $n \\mapsto n+1$ is $2$, since $2+1=3$.
And $2 \\in \\text{range}(4)$ since $2 < 4$.
"

/-- 3 is in the image of (n ↦ n + 1) applied to range 4. -/
Statement : (3 : ℕ) ∈ (Finset.range 4).image (fun n => n + 1) := by
  Hint "Use `rw [Finset.mem_image]` to convert the membership goal
  into an existential: you need to find some `x ∈ range 4` with
  `x + 1 = 3`."
  rw [Finset.mem_image]
  Hint "The goal is `∃ x ∈ Finset.range 4, x + 1 = 3`.
  Which `x` satisfies `x + 1 = 3`? Solve: `x = 2`.
  Use `use 2` to provide the witness."
  Hint (hidden := true) "Try `use 2`."
  use 2
  Hint "After `use 2`, Lean automatically verified that `2 + 1 = 3`
  (by computation). The remaining goal is `2 ∈ Finset.range 4`.
  Rewrite with `rw [Finset.mem_range]` to get `2 < 4`, then `omega`."
  rw [Finset.mem_range]
  omega

Conclusion "
The image membership pattern:
1. `rw [Finset.mem_image]` — reduces to an existential
2. `use witness` — provide the preimage (Lean auto-verifies `f x = y`)
3. Prove `x ∈ s` (the remaining goal)

The challenge is step 2: choosing the right witness. You need to solve
$f(x) = y$ for $x$ — here, $x + 1 = 3$ gives $x = 2$.

In plain math: to show $y \\in f(S)$, exhibit $x \\in S$ with $f(x) = y$.
"

/-- `Finset.image f s` is the finset of all values `f x` for `x ∈ s`.

## Notation
`s.image f` or `Finset.image f s`

## Key lemma
`Finset.mem_image : y ∈ s.image f ↔ ∃ x ∈ s, f x = y`

## Example
`(Finset.range 3).image (fun n => n * 2)` gives the finset containing 0, 2, and 4.
-/
DefinitionDoc Finset.image as "Finset.image"

/-- `Finset.mem_image` states that `y ∈ s.image f ↔ ∃ x ∈ s, f x = y`.

## Syntax
```
rw [Finset.mem_image]       -- in the goal
rw [Finset.mem_image] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `y ∈ s.image f`.
After rewriting, the goal becomes an existential that you solve
with `use`.

## Example
```
-- Goal: 6 ∈ (Finset.range 5).image (fun n => n * 2)
rw [Finset.mem_image]
-- Goal: ∃ x ∈ Finset.range 5, x * 2 = 6
use 3
```
-/
TheoremDoc Finset.mem_image as "Finset.mem_image" in "Finset"

TheoremTab "Finset"
NewDefinition Finset.image
NewTheorem Finset.mem_image

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
