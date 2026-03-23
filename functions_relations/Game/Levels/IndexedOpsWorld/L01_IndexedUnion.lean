import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 1

Title "Indexed Union"

Introduction "
# Indexed Unions

In Set Operations World, you learned that `s ∪ t` corresponds to `∨`:
an element is in the union if it is in `s` **or** in `t`. But what if
you have not just two sets, but a whole **family** of sets — one for
each value of some index?

If `s : ι → Set α` is a family of sets indexed by `ι`, the
**indexed union** `⋃ i, s i` collects every element that belongs to
at least one set in the family:

$$x \\in \\bigcup_i s_i \\;\\Longleftrightarrow\\; \\exists\\, i,\\; x \\in s_i$$

The binary union `s ∪ t` is the special case with a two-element index
(`Bool`). The indexed version generalizes `∨` to `∃`:

| Operation | Notation | Logical meaning |
|---|---|---|
| Binary union | `s ∪ t` | `x ∈ s ∨ x ∈ t` |
| Indexed union | `⋃ i, s i` | `∃ i, x ∈ s i` |

**New tool**: `rw [Set.mem_iUnion]` converts `x ∈ ⋃ i, s i` into
`∃ i, x ∈ s i`. After that, you provide the witness index with `use`.

**Your task**: The family `s k = {n : ℕ | n % 3 = k}` for `k : ℕ`
gives one set for each possible remainder mod 3 (and more).
Prove that `5` belongs to this indexed union by finding the right
remainder class.
"

NewTheorem Set.mem_iUnion
NewDefinition Set.iUnion
TheoremTab "Set"

/-- 5 belongs to the indexed union of remainder classes mod 3. -/
Statement : 5 ∈ ⋃ k : ℕ, {n : ℕ | n % 3 = k} := by
  Hint "The goal involves `⋃`. Use `rw [Set.mem_iUnion]` to convert
  it to an existential: `∃ k, 5 ∈ ...`."
  rw [Set.mem_iUnion]
  Hint "The goal is now `∃ k : ℕ, 5 ∈ ...`. You need to provide
  the witness — which remainder class does 5 belong to?

  Since `5 % 3 = 2`, the witness is `k = 2`. Use `use 2`."
  Hint (hidden := true) "`use 2` provides the witness `k = 2`."
  use 2
  Hint "The goal is now a set membership that unfolds to `5 % 3 = 2`.
  Use `show 5 % 3 = 2` to make this explicit, then `omega`."
  Hint (hidden := true) "`show 5 % 3 = 2` then `omega`."
  show 5 % 3 = 2
  omega

Conclusion "
You proved membership in an indexed union. The pattern is:

```
rw [Set.mem_iUnion]   -- convert ⋃ to ∃
use witness           -- provide the index
...                   -- prove membership in that particular set
```

**The key insight**: `⋃ i, s i` generalizes `∪` from two sets to a
whole family. Just as `∪` corresponds to `∨`, the indexed `⋃`
corresponds to `∃`. To prove something is in the union, you exhibit
a witness index.

In ordinary math: \"$5 \\in \\bigcup_{k \\in \\mathbb{N}} \\{n : n \\bmod 3 = k\\}$
because $5 \\bmod 3 = 2$, so $5$ is in the $k=2$ set.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
