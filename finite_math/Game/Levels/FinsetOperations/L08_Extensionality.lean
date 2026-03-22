import Game.Metadata

World "FinsetOperations"
Level 8

Title "Extensionality"

Introduction "
# The ext Tactic: Proving Set Equality Element-wise

Two finsets are equal when they have the same elements:

$$s = t \\;\\longleftrightarrow\\; \\forall x,\\; x \\in s \\;\\leftrightarrow\\; x \\in t$$

This is `Finset.ext_iff`. The `ext` tactic automates this: on a goal
`s = t` where `s` and `t` are finsets, `ext x` introduces a variable
`x` and changes the goal to `x ∈ s ↔ x ∈ t`.

```
ext x
-- Goal becomes: x ∈ s ↔ x ∈ t
```

Then you prove the biconditional with `constructor`, giving two
implications.

Compare this with `Subset.antisymm` from the previous level:
- `Subset.antisymm` creates two subset goals (`⊆` in both directions)
- `ext` creates one biconditional goal (`↔`)

They're logically equivalent, but `ext` is more direct.

**Your task**: Given that every element of `s` is in `t` and vice versa,
prove `s = t` using `ext`.
"

/-- If s and t have the same elements, they are equal. -/
Statement (s t : Finset ℕ) (hs : ∀ x, x ∈ s → x ∈ t) (ht : ∀ x, x ∈ t → x ∈ s) :
    s = t := by
  Hint "Use `ext x` to introduce a variable and convert the
  equality into an element-wise biconditional."
  ext x
  Hint "The goal is `x ∈ s ↔ x ∈ t`. Use `constructor` to split
  the biconditional into two implications."
  constructor
  · Hint "The goal is `x ∈ s → x ∈ t`. You have `hs : ∀ x, x ∈ s → x ∈ t`.
    Use `exact hs x` to close it."
    exact hs x
  · Hint "The goal is `x ∈ t → x ∈ s`. Use `exact ht x`."
    exact ht x

Conclusion "
The `ext` tactic is the standard way to prove finset equality in Lean.
The pattern:

1. `ext x` — introduces a variable `x` and converts `s = t` to `x ∈ s ↔ x ∈ t`
2. `constructor` — splits the biconditional into two implications
3. Prove each direction

In this level, the hypotheses `hs` and `ht` handed you the
implications directly. In the next level, you'll prove an abstract
set identity where you need to do the element-chasing yourself.

The key insight: *finsets are determined by their elements*. This is
the **extensionality principle** — two collections are equal when they
have the same members.

**`ext` as a transferable strategy**: This is the third time you've
used `ext`, and each time it does the same thing in a different context:
- **Fin elements** (MeetFin L15): `ext` reduces `a = b` to `a.val = b.val`
  — two indices are equal when their values are equal
- **Functions** (FinTuples L12): `ext i` reduces `f = g` to `f i = g i`
  — two functions are equal when they agree at every input
- **Finsets** (this level): `ext x` reduces `s = t` to `x ∈ s ↔ x ∈ t`
  — two sets are equal when they have the same elements

The unifying principle: **ext reduces equality of structured types to
equality of components**. Whenever you see `a = b` for a structured
type, try `ext` — it will find the right decomposition automatically.

**Why extensionality?** This is a design choice, not an inevitability.
A list like `[1, 1, 2]` is different from `[1, 2]` — lists track
multiplicity and order. A *multiset* like `\\{\\!\\{1, 1, 2\\}\\!\\}` differs from
`\\{\\!\\{1, 2\\}\\!\\}` — multisets track multiplicity but not order. A finset
like `\\{1, 1, 2\\}` equals `\\{1, 2\\}` — finsets track neither multiplicity
nor order, only *which elements are present*. Extensionality is what
makes a finset a finset rather than a list or multiset.

**The ext-unfold-logic recipe**: From now on, most set identity proofs
will follow the same three-phase pattern:
1. **ext** — `ext x` reduces set equality to element-wise logic
2. **unfold** — `rw [mem_union]`, `rw [mem_inter]`, etc.
   (or `simp only [...]`) to convert membership into pure logic
3. **logic** — `constructor`, `cases`, `left`/`right`,
   `.1`/`.2` to prove the resulting propositional equivalence

We'll call this the **ext-unfold-logic** recipe. Every set identity in
the remaining levels follows this recipe. When you see a finset equality
to prove, think 'ext-unfold-logic' and the three steps will guide you.
"

/-- `Finset.ext_iff` states that `s = t ↔ ∀ x, x ∈ s ↔ x ∈ t`.

This is the theorem underlying the `ext` tactic for finsets.

## Syntax
```
rw [Finset.ext_iff]  -- converts s = t to ∀ x, x ∈ s ↔ x ∈ t
```

## When to use it
Usually you would use the `ext` tactic instead, which is more
convenient. Use `ext_iff` directly when you need the iff form
(e.g., for rewriting in the reverse direction).
-/
TheoremDoc Finset.ext_iff as "Finset.ext_iff" in "Finset"

NewTheorem Finset.ext_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm
