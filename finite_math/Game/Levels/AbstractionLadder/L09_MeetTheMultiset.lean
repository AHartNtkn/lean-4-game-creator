import Game.Metadata

World "AbstractionLadder"
Level 9

Title "Meet the Multiset"

Introduction "
# Climbing the Ladder: List → Multiset

A `Multiset α` is a **list quotiented by permutation**. Two lists
that are permutations of each other become the *same* multiset.

The coercion `↑l` (or `(↑l : Multiset α)`) sends a `List α` to the
corresponding `Multiset α`. The key bridge lemma is:

`Multiset.coe_eq_coe : (↑l₁ : Multiset α) = ↑l₂ ↔ l₁.Perm l₂`

In other words: two lists give the same multiset **if and only if**
they are permutations of each other. This is exactly what 'quotient
by permutation' means.

**What's lost**: Order. `[2, 1, 3]` and `[3, 2, 1]` are different
lists but the same multiset.

**What's kept**: Multiplicities. A multiset remembers *how many* of
each element it contains.

**Your task**: Prove that `[2, 1, 3]` and `[3, 2, 1]` give the same
multiset. You'll need to rewrite with `Multiset.coe_eq_coe` and then
prove the permutation — using the swap-chaining technique from L07.

**Tip**: If term-mode `have` feels hard to type in one go, you can
use `have h1 : ... := by exact ...` for intermediate feedback.
"

/-- Two permuted lists give the same multiset. -/
Statement : (↑[2, 1, 3] : Multiset ℕ) = ↑[3, 2, 1] := by
  Hint "Use `rw [Multiset.coe_eq_coe]` to convert the multiset equality
  into a list permutation."
  rw [Multiset.coe_eq_coe]
  Hint "Now prove `[2, 1, 3] ~ [3, 2, 1]`. You need to find an
  **intermediate list** that connects them — a list reachable from
  `[2, 1, 3]` by one swap AND from which `[3, 2, 1]` is reachable
  by one swap.

  **How to find the intermediate**: Look at the first element.
  The source starts with `2`, the target starts with `3`. You need
  `3` at the front eventually. Try keeping `2` at the front for the
  first swap (rearrange the tail), then swap `2` and `3` in the
  second step. So: `[2, 1, 3] → [2, 3, 1] → [3, 2, 1]`."
  Hint (hidden := true) "Chain two swaps via `[2, 3, 1]`:
  `have h1 : List.Perm [2, 1, 3] [2, 3, 1] := List.Perm.cons 2 (List.Perm.swap 3 1 [])`
  `have h2 : List.Perm [2, 3, 1] [3, 2, 1] := List.Perm.swap 3 2 [1]`
  `exact h1.trans h2`"
  have h1 : List.Perm [2, 1, 3] [2, 3, 1] := List.Perm.cons 2 (List.Perm.swap 3 1 [])
  have h2 : List.Perm [2, 3, 1] [3, 2, 1] := List.Perm.swap 3 2 [1]
  exact h1.trans h2

Conclusion "
You just proved that two lists give the same multiset by showing they
are permutations. The bridge `Multiset.coe_eq_coe` converts between
these two perspectives.

This is the first layer of the abstraction ladder in action:
- As **lists**: `[2, 1, 3] ≠ [3, 2, 1]` (different order)
- As **multisets**: `↑[2, 1, 3] = ↑[3, 2, 1]` (order forgotten)

In plain math: as multisets, $\\{\\!\\{1, 2, 3\\}\\!\\} = \\{\\!\\{3, 2, 1\\}\\!\\}$
because they contain the same elements with the same multiplicities.

**Why does Finset use Multiset internally, not List + Nodup directly?**
The answer is proof economy. If Finset were built directly on List,
every operation (union, intersection, insert) would need to carry
permutation proofs showing that the result doesn't depend on element
order. By quotienting List by permutation *first* to get Multiset,
the 'order doesn't matter' property becomes *definitional* — it's
baked into the type. Then Finset only needs to add the Nodup constraint
on top. This two-step design means fewer proof obligations at every
level of the library.
"

/-- `Multiset` is a list quotiented by permutation. A `Multiset α`
is an unordered collection of elements that may contain duplicates.

## Key operations
- `↑l` — coerce a `List α` to `Multiset α`
- `a ::ₘ m` — cons an element to a multiset
- `Multiset.card m` — number of elements (with multiplicity)
- `Multiset.count a m` — how many times `a` appears

## Key bridge lemma
- `Multiset.coe_eq_coe : ↑l₁ = ↑l₂ ↔ l₁.Perm l₂`
-/
DefinitionDoc Multiset as "Multiset"

/-- `Multiset.coe_eq_coe` states that
`(↑l₁ : Multiset α) = ↑l₂ ↔ l₁.Perm l₂`.

Two lists give the same multiset if and only if they are permutations.

## Syntax
```
rw [Multiset.coe_eq_coe]
```

## When to use it
When you need to prove two list coercions give equal multisets,
or when you need to extract a permutation from a multiset equality.
-/
TheoremDoc Multiset.coe_eq_coe as "Multiset.coe_eq_coe" in "Multiset"

TheoremTab "Multiset"
NewDefinition Multiset
NewTheorem Multiset.coe_eq_coe

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
