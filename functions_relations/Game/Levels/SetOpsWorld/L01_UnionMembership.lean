import Game.Metadata

World "SetOpsWorld"
Level 1

Title "Union Membership"

TheoremTab "Set"

Introduction "
# Set Operations: Union

In the last two worlds, you learned that sets are predicates and that
subset/equality proofs reduce to propositional logic. Now you will learn
the **set operations** — union, intersection, complement, and difference —
and see that each one corresponds to a logical connective.

The first operation is **union**. The union of two sets `s` and `t`,
written `s ∪ t`, contains every element that belongs to `s` **or** `t`
(or both):

$$x \\in s \\cup t \\;\\;\\Longleftrightarrow\\;\\; x \\in s \\;\\lor\\; x \\in t$$

So union IS disjunction. When you need to prove `x ∈ s ∪ t`, you are
proving a disjunction. You choose which side to prove using two new
tactics:

- `left` — reduces the goal to the left disjunct (`x ∈ s`)
- `right` — reduces the goal to the right disjunct (`x ∈ t`)

**Your task**: Prove that 3 is in the union of two sets. Since $3 < 5$,
the left set contains 3, so use `left`.

**Proof plan**:
1. `left` — choose the left disjunct (3 is in the left set)
2. `show 3 < 5` — unfold the set-builder membership
3. `omega` — close the arithmetic goal
"

/-- 3 belongs to the union because it satisfies the left set's predicate. -/
Statement : (3 : ℕ) ∈ ({n : ℕ | n < 5} ∪ {n | Even n}) := by
  Hint "The goal is a union membership. Since `∪` means `∨`, you need to
  choose a side. 3 is less than 5, so it belongs to the left set.
  Use `left` to select the left disjunct."
  Branch
    show 3 < 5 ∨ Even 3
    Hint "Good — you can see the `∨` explicitly now. Use `left` to
    select the left side, then close the arithmetic."
    left
    omega
  left
  Hint "The goal is now membership in the left set. Use `show 3 < 5`
  to unfold the set-builder notation, then `omega`."
  Hint (hidden := true) "`show 3 < 5` converts the goal to arithmetic
  form. Then `omega` closes it."
  show 3 < 5
  omega

Conclusion "
You proved union membership by choosing a side with `left`.

The key insight: **union (`∪`) corresponds to disjunction (`∨`)**. To
prove `x ∈ s ∪ t`, you prove `x ∈ s` (using `left`) or `x ∈ t`
(using `right`). This is the first of four set-operation-to-logic
correspondences you will learn in this world:

| Operation | Logic |
|---|---|
| `∪` (union) | `∨` (or) |

In ordinary math: \"$3 \\in \\{n \\mid n < 5\\} \\cup \\{n \\mid \\text{Even}(n)\\}$
because $3 < 5$.\"

You could also have written `show 3 < 5 ∨ Even 3` first to see the
full unfolding from set notation to propositions. Try it if you want
to redo the level — it makes the `∪` = `∨` connection visible.
"

/-- `s ∪ t` (typed `\\cup` or `\\union`) is the **union** of sets `s` and `t`.

An element belongs to `s ∪ t` if it belongs to `s` **or** `t`:
$$x \\in s \\cup t \\iff x \\in s \\lor x \\in t$$

## Proof strategies

**To prove** `x ∈ s ∪ t`:
- `left` then prove `x ∈ s`, OR
- `right` then prove `x ∈ t`

**Given** `h : x ∈ s ∪ t`:
- `cases h with | inl hs | inr ht` to split into two cases

## Warning
You must **choose** a side: `left` or `right`. You cannot prove both
and let Lean pick — you must commit to one.
-/
DefinitionDoc Set.union as "Set.union"

NewTactic left right
NewDefinition Set.union

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
