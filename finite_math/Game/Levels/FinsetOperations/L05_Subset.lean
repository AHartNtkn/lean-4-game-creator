import Game.Metadata

World "FinsetOperations"
Level 5

Title "Subset"

Introduction "
# Subset: Every Element of One is in the Other

The **subset** relation `s ⊆ t` means every element of `s` is also
in `t`. The characterization is:

$$s \\subseteq t \\;\\longleftrightarrow\\; \\forall x,\\; x \\in s \\;\\to\\; x \\in t$$

In Lean, this is `Finset.subset_iff`:
```
Finset.subset_iff : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t
```

(The `⦃x⦄` notation means 'strict implicit' — for our purposes, it
behaves just like `(x)`. You introduce it with `intro x` as usual.)

The proof move: `rw [Finset.subset_iff]` converts a subset goal into
a universally quantified implication. Then `intro x hx` gives you an
element `x` and a hypothesis `hx : x ∈ s`, and you must prove `x ∈ t`.

**Your task**: Prove that $\\{1, 2\\} \\subseteq \\{1, 2, 3\\}$.
"

/-- {1, 2} is a subset of {1, 2, 3}. -/
Statement : ({1, 2} : Finset ℕ) ⊆ {1, 2, 3} := by
  Hint "Use `rw [Finset.subset_iff]` to unfold the subset relation
  into a universally quantified implication."
  rw [Finset.subset_iff]
  Hint "The goal is a universally quantified implication: for any `x`
  in the first set, `x` is in the second set.
  Use `intro x hx` to introduce an element and its membership hypothesis."
  intro x hx
  Hint "Now unfold `hx` to see what `x` could be:
  `rw [Finset.mem_insert, Finset.mem_singleton] at hx`."
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  Hint "After unfolding, `hx : x = 1 ∨ x = 2`. Use `cases hx with`
  to handle each possibility."
  cases hx with
  | inl h =>
    Hint (hidden := true) "`rw [{h}]` substitutes the value, then prove
    membership: `rw [Finset.mem_insert]; left; rfl`."
    rw [h]
    rw [Finset.mem_insert]
    left
    rfl
  | inr h =>
    Hint (hidden := true) "`rw [{h}]` substitutes the value, then
    `rw [Finset.mem_insert]; right; rw [Finset.mem_insert]; left; rfl`."
    rw [h]
    rw [Finset.mem_insert]
    right
    rw [Finset.mem_insert]
    left
    rfl

Conclusion "
The pattern for subset proofs:
1. `rw [Finset.subset_iff]` — unfolds `s ⊆ t` to `∀ x ∈ s, x ∈ t`
2. `intro x hx` — introduce an element and its membership in `s`
3. `rw [mem_insert, ...] at hx` — unfold what `x` could be
4. `cases hx` — handle each possibility
5. In each case: substitute and prove membership in `t`

This is an **element-chasing** proof: you take an arbitrary element of
`s` and show it must be in `t`. The case analysis on `hx` ensures you
consider every element of `s`.

In plain mathematics: to show $A \\subseteq B$, take any $x \\in A$ and
show $x \\in B$.

The subset relation $\\subseteq$ is a **partial order** — it satisfies
three properties:
- **Reflexivity**: $s \\subseteq s$ (every set is a subset of itself —
  `intro x hx; exact hx`)
- **Transitivity**: if $s \\subseteq t$ and $t \\subseteq u$, then
  $s \\subseteq u$ (chain the element-chasing: any $x \\in s$ is in $t$
  by the first, then in $u$ by the second)
- **Antisymmetry**: if $s \\subseteq t$ and $t \\subseteq s$, then $s = t$
  (you'll see this in Level 7 as `Subset.antisymm`)

These three properties make finsets with $\\subseteq$ a **partially ordered
set** — a structure you'll study in depth in the orders and lattices course.
"

/-- `Finset.subset_iff` states that `s ⊆ t ↔ ∀ x ∈ s, x ∈ t`.

## Syntax
```
rw [Finset.subset_iff]  -- unfolds ⊆ to ∀-implication
```

## When to use it
When the goal is `s ⊆ t`. After rewriting, use `intro x hx` to
introduce an element and prove its membership in `t`.

## Example
```
-- Goal: {1, 2} ⊆ {1, 2, 3}
rw [Finset.subset_iff]
-- Goal: ∀ x ∈ {1, 2}, x ∈ {1, 2, 3}
intro x hx
-- hx : x ∈ {1, 2}, Goal: x ∈ {1, 2, 3}
```
-/
TheoremDoc Finset.subset_iff as "Finset.subset_iff" in "Finset"

NewTheorem Finset.subset_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right
