import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 15

Title "Powerset"

Introduction "
# The Powerset

The **powerset** `𝒫 s` is the set of all subsets of `s`:

$$t \\in \\mathcal{P}(s) \\;\\Longleftrightarrow\\; t \\subseteq s$$

Notice that `𝒫 s` is a set whose *elements are sets*. While `∈`, `∪`,
`∩`, etc. are about elements belonging to sets, the powerset is about
sets belonging to a collection of sets.

**New tool**: `rw [Set.mem_powerset_iff]` converts `t ∈ 𝒫 s` into
`t ⊆ s`. After that, you prove a subset relation — which you
already know how to do from Subset World.

**Notation**: Type `𝒫` as `\\powerset` or `\\P`.

**Your task**: Prove that `{n : ℕ | n < 3}` is in the powerset of
`{n : ℕ | n < 5}` — that is, every number less than 3 is also less
than 5.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- The set of numbers less than 3 is in the powerset of numbers less than 5. -/
Statement : {n : ℕ | n < 3} ∈ 𝒫 {n : ℕ | n < 5} := by
  Hint "The goal involves `𝒫`. Use `rw [Set.mem_powerset_iff]` to convert
  to a subset relation."
  rw [Set.mem_powerset_iff]
  Hint "The goal is now a subset relation. This is a familiar subset
  proof from Subset World. Start with `intro x hx`."
  intro x hx
  Hint "You have a hypothesis about `x` being in the left set, and
  need to show `x` is in the right set. Unfold both with `show`
  and `change`."
  Hint (hidden := true) "`show x < 5` to unfold the goal. Then
  `change x < 3 at hx` to unfold the hypothesis. Then `omega`."
  show x < 5
  change x < 3 at hx
  omega

Conclusion "
You proved powerset membership. The pattern is:

```
rw [Set.mem_powerset_iff]   -- convert 𝒫 to ⊆
intro x hx                  -- start the subset proof
...                          -- show membership transfers
```

**The correspondence**: Powerset membership is subset. This is a
\"meta-level\" operation — instead of asking whether an element is in
a set, you ask whether a set is in a collection of sets.

| Expression | Type | Meaning |
|---|---|---|
| `x ∈ s` | `Prop` | element membership |
| `s ⊆ t` | `Prop` | every element of s is in t |
| `t ∈ 𝒫 s` | `Prop` | same as `t ⊆ s` |

**Looking ahead**: The powerset will reappear when we study images
and preimages of set families. In Cantor World, you will prove that
the powerset of a set is always strictly larger than the set itself —
using a diagonal argument unlike anything in this course so far.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
