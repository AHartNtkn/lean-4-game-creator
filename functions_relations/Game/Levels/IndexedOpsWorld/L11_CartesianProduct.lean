import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 11

Title "Cartesian Product"

Introduction "
# Cartesian Products of Sets

The **cartesian product** `s ×ˢ t` of two sets `s : Set α` and
`t : Set β` is the set of all pairs `(a, b)` with `a ∈ s` and `b ∈ t`:

$$(a, b) \\in s \\times t \\;\\Longleftrightarrow\\; a \\in s \\;\\wedge\\; b \\in t$$

This is yet another set operation that reduces to a logical connective —
this time `∧`, just like `∩`. The difference is that `∩` combines
two sets of the **same** type, while `×ˢ` combines sets of
**different** types into a set of pairs.

**New tool**: `rw [Set.mem_prod]` converts `p ∈ s ×ˢ t` into
`p.1 ∈ s ∧ p.2 ∈ t`. After that, use `constructor` to split the
conjunction, just like with `∩`.

**Notation**: The `ˢ` superscript in `×ˢ` stands for \"set\". It
distinguishes the set product from the type product `α × β`. You type
it as `\\x\\^s` or `\\times\\^s`.

**Your task**: Prove that `(2, 3)` belongs to the product of the even
numbers with the numbers less than 5.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod
NewDefinition Set.iUnion Set.iInter Set.prod
TheoremTab "Set"

/-- (2, 3) belongs to the product of even numbers with numbers less than 5. -/
Statement : (2, 3) ∈ ({n : ℕ | Even n} ×ˢ {n : ℕ | n < 5}) := by
  Hint "The goal involves `×ˢ`. Use `rw [Set.mem_prod]` to convert
  to a conjunction: `2 ∈ ... ∧ 3 ∈ ...`."
  rw [Set.mem_prod]
  Hint "The goal is a conjunction. Use `constructor` to split it into
  two parts."
  constructor
  · Hint "The first component goal unfolds to `Even 2`.
    Use `show Even 2` to make it explicit."
    Hint (hidden := true) "`show Even 2` then `exact ⟨1, rfl⟩`.

    Recall: `Even n` means `∃ k, n = k + k`. The witness for
    `Even 2` is `k = 1`, since `2 = 1 + 1`."
    show Even 2
    exact ⟨1, rfl⟩
  · Hint "The second component goal unfolds to `3 < 5`.
    Use `show 3 < 5` then `omega`."
    Hint (hidden := true) "`show 3 < 5` then `omega`."
    show 3 < 5
    omega

Conclusion "
You proved membership in a cartesian product. The pattern is:

```
rw [Set.mem_prod]    -- convert ×ˢ to ∧
constructor          -- split into two membership goals
· ...                -- prove the first component
· ...                -- prove the second component
```

**The correspondence**: `×ˢ` is to pairs what `∩` is to single
elements — both reduce to `∧`. The difference is structural:
`∩` operates on two sets of the same type, while `×ˢ` combines
sets of (potentially) different types.

In ordinary math: \"$(2, 3) \\in \\{\\text{evens}\\} \\times \\{n : n < 5\\}$
because $2$ is even and $3 < 5$.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
