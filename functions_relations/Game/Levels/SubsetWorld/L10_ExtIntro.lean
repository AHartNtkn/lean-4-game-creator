import Game.Metadata

World "SubsetWorld"
Level 10

Title "Set Equality with ext"

Introduction "
# Extensionality: When Two Sets Are Equal

Two sets are equal when they have exactly the same elements:

$$s = t \\;\\;\\Longleftrightarrow\\;\\; \\forall\\, x,\\; x \\in s \\leftrightarrow x \\in t$$

This is the **Axiom of Extensionality** — one of the foundational
axioms of set theory. It says that a set is nothing more than its
elements: two sets with the same members are the same set, regardless
of how they are described. The tactic `ext x`
converts a set equality goal into: for each `x`, prove the membership
biconditional `x ∈ s ↔ x ∈ t`.

After `ext x`, the goal becomes an `↔`. Use `constructor` to split it
into two implications (forward and backward), then prove each direction.

After `constructor`, you will see the `·` (focus dot) for the first time.
When Lean creates multiple subgoals, `·` **focuses** on one subgoal at
a time. Write `· tactic` to apply `tactic` to the current subgoal only.
After that subgoal is closed, the next `·` picks up the next subgoal.
Think of `·` as \"now working on this case.\"

**Your task**: Prove that `{n | n < 3 ∧ n < 5} = {n | n < 3}`.

The conjunction `n < 3 ∧ n < 5` is equivalent to just `n < 3` because
`n < 3` already implies `n < 5`. So the second condition is redundant.

This level is longer than previous ones — the proof has several steps.
Do not worry: each step is guided by hints, and the math is simple.
The length comes from the proof structure, not from difficulty.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔` into two directions
3. **Forward** (`→`): given `x < 3 ∧ x < 5`, extract `x < 3`
4. **Backward** (`←`): given `x < 3`, build `x < 3 ∧ x < 5`
"

/-- A conjunction with a weaker condition is equivalent to the
stronger condition alone. -/
Statement : {n : ℕ | n < 3 ∧ n < 5} = {n : ℕ | n < 3} := by
  Hint "The goal is a set equality. Use `ext x` to reduce it to
  \"for all x, membership in the left equals membership in the right\"."
  ext x
  Hint "The goal is now an `↔` (biconditional). Use `constructor` to
  split it into two implications: forward (`→`) and backward (`←`)."
  constructor
  -- Forward direction: x ∈ {n | n < 3 ∧ n < 5} → x ∈ {n | n < 3}
  · Hint "The forward direction: assume membership in the left set.
    The hypothesis encodes a conjunction `x < 3 ∧ x < 5`.

    The `.1` and `.2` projections extract components from a conjunction:
    if `hx : P ∧ Q`, then `hx.1 : P` and `hx.2 : Q`.

    Since you need `x < 3` and the hypothesis is `x < 3 ∧ x < 5`,
    you can use `.1` to extract the first component."
    Hint (hidden := true) "`intro hx` then `exact hx.1` extracts the
    first component of the conjunction.

    Alternatively: `intro ⟨h1, _⟩` destructures on introduction,
    then `exact h1`."
    Branch
      -- Path: intro with destructuring
      intro ⟨h1, _⟩
      exact h1
    Branch
      intro h
      obtain ⟨h1, _⟩ := h
      exact h1
    intro hx
    Hint "`hx` is a conjunction `x < 3 ∧ x < 5`. Use `exact hx.1`
    to extract the first component (`x < 3`), which matches the goal."
    exact hx.1
  -- Backward direction: x ∈ {n | n < 3} → x ∈ {n | n < 3 ∧ n < 5}
  · Hint "The backward direction: assume `x` is in the right set and
    prove it is in the left set. The goal is a conjunction —
    use `constructor` to split it."
    intro h
    Hint "The goal is definitionally `x < 3 ∧ x < 5`. Use `constructor`
    to split into two goals: `x < 3` and `x < 5`."
    constructor
    · Hint "`h` is definitionally `x < 3`, which matches the goal.
      Use `exact h`."
      exact h
    · Hint "The goal is `x < 5`. You need `x < 3` to derive this —
      but `h` is wrapped in set notation. Use `change x < 3 at h`
      to unwrap, then `omega`."
      Hint (hidden := true) "After `change x < 3 at h`, use `omega`
      to derive `x < 5` from `x < 3`."
      change x < 3 at h
      omega

Conclusion "
You proved your first set equality using `ext`! The structure was:

```
ext x          -- reduce to: ∀ x, x ∈ LHS ↔ x ∈ RHS
constructor    -- split the ↔ into → and ←
· ...          -- prove the forward direction
· ...          -- prove the backward direction
```

**Why `ext` works**: `ext` applies the **extensionality** axiom for
sets: two sets are equal if and only if they have the same elements.
This converts a single equation into universally quantified membership
equivalences — exactly the type of claim you can prove element by
element.

In ordinary math, this proof would read: \"We show the sets are equal
by double inclusion. If $n < 3$ and $n < 5$, then certainly $n < 3$.
Conversely, if $n < 3$, then also $n < 5$ (since $3 < 5$), so
$n < 3 \\wedge n < 5$.\"

**The `·` (focus dot)**: After `constructor` splits a goal into two
subgoals, `·` focuses on one at a time. This keeps your proof
organized — you handle one case completely before moving to the next.
You will use `·` in nearly every proof that involves `constructor`.

**Dot projections on `∧`**: If `hx : P ∧ Q`, then `hx.1 : P` and
`hx.2 : Q`. This is the quickest way to extract one component of a
conjunction. The same `.1`/`.2` pattern works on `↔` (biconditionals)
too — you will use it later to extract the forward and backward
implications.

**Destructuring `intro`**: When a hypothesis is a conjunction `P ∧ Q`,
you can write `intro ⟨h1, h2⟩` to introduce and split it in one step,
instead of `intro h` followed by `obtain ⟨h1, h2⟩ := h`. This
shorthand will be especially useful in the next world when working
with intersections (`∩`), which are defined as conjunctions.

The `ext` tactic is the primary tool for set equality proofs in Lean.
You will use it frequently throughout this course.
"

/-- `ext x` applies the extensionality principle to convert a set
equality `s = t` into a membership biconditional for each element.

## Syntax
```
ext x      -- introduces x and produces goal: x ∈ s ↔ x ∈ t
```

## When to use it
When the goal is `s = t` for two sets. After `ext x`, you get
the goal `x ∈ s ↔ x ∈ t`, which you split with `constructor` into
two directions.

## Example
```
-- Goal: {n | n < 3} = {n | n ≤ 2}
ext x
-- Goal: x ∈ {n | n < 3} ↔ x ∈ {n | n ≤ 2}
constructor
· intro h; ...  -- forward direction
· intro h; ...  -- backward direction
```

## Warning
`ext` works for sets, functions, and other extensional types. For
sets, it always produces a membership `↔`. Do not confuse with
`exact` (which closes a goal with a proof term).
-/
TacticDoc ext

NewTactic ext

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.Subset.antisymm le_antisymm HasSubset.Subset.antisymm subset_antisymm Set.eq_of_subset_of_subset LE.le.antisymm Set.ext_iff
