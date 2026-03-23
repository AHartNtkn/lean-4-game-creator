import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 2

Title "Indexed Intersection"

Introduction "
# Indexed Intersections

Just as `⋃` generalizes `∪`, the **indexed intersection** `⋂ i, s i`
generalizes `∩`:

$$x \\in \\bigcap_i s_i \\;\\Longleftrightarrow\\; \\forall\\, i,\\; x \\in s_i$$

An element is in the indexed intersection if it belongs to **every**
set in the family. The binary intersection `s ∩ t` is the special
case with a two-element index:

| Operation | Notation | Logical meaning |
|---|---|---|
| Binary intersection | `s ∩ t` | `x ∈ s ∧ x ∈ t` |
| Indexed intersection | `⋂ i, s i` | `∀ i, x ∈ s i` |

**New tool**: `rw [Set.mem_iInter]` converts `x ∈ ⋂ i, s i` into
`∀ i, x ∈ s i`. After that, you introduce the universally quantified
variable with `intro`.

**About `Fin`**: The index type here is `Fin 4`, which represents
the natural numbers less than 4: `{0, 1, 2, 3}`. After `intro k`,
you get `k : Fin 4`. Use `k.val` to access its numerical value.
This bounded type ensures the intersection is over finitely many sets.

**Your task**: The family `s k = {n : ℕ | k.val ≤ n}` for `k : Fin 4`
gives four sets: {n | 0 ≤ n}, {n | 1 ≤ n}, {n | 2 ≤ n}, {n | 3 ≤ n}.
Prove that `10` belongs to all of them.
"

NewTheorem Set.mem_iUnion Set.mem_iInter
NewDefinition Set.iUnion Set.iInter
TheoremTab "Set"

/-- 10 belongs to the indexed intersection of lower-bound sets. -/
Statement : 10 ∈ ⋂ k : Fin 4, {n : ℕ | k.val ≤ n} := by
  Hint "The goal involves `⋂`. Use `rw [Set.mem_iInter]` to convert
  it to a universal statement: `∀ k, 10 ∈ ...`."
  rw [Set.mem_iInter]
  Hint "The goal is now `∀ k : Fin 4, 10 ∈ ...`. Use `intro k` to
  introduce the index variable."
  intro k
  Hint "The goal is a set membership that unfolds to `k.val ≤ 10`.
  Use `show k.val ≤ 10` to make it explicit, then `omega`
  (since `k.val < 4` and `4 ≤ 10`)."
  Hint (hidden := true) "`show k.val ≤ 10` then `omega`."
  show k.val ≤ 10
  omega

Conclusion "
You proved membership in an indexed intersection. The pattern is:

```
rw [Set.mem_iInter]   -- convert ⋂ to ∀
intro i               -- introduce the index
...                   -- prove membership for that index
```

**The key insight**: `⋂ i, s i` generalizes `∩` from two sets to a
whole family. Just as `∩` corresponds to `∧`, the indexed `⋂`
corresponds to `∀`. To prove something is in the intersection, you
must show it is in every set of the family — for all indices.

**Summary of the ∪/∩ generalization**:

| Binary | Indexed | Logic |
|---|---|---|
| `s ∪ t` | `⋃ i, s i` | `∨` → `∃` |
| `s ∩ t` | `⋂ i, s i` | `∧` → `∀` |

**The binary-as-indexed connection**: The binary intersection `s ∩ t`
is really the special case of `⋂` over a two-element index. Likewise,
`s ∪ t` is the special case of `⋃` over two elements. Every binary
set identity you proved in Set Operations World has an indexed
generalization — and the proofs follow the same logical structure,
with `∧`/`∨` replaced by `∀`/`∃`.

In ordinary math: \"$10 \\in \\bigcap_{k=0}^{3} \\{n : k \\le n\\}$
because for every $k \\in \\{0,1,2,3\\}$, we have $k \\le 10$.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith fin_cases
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
