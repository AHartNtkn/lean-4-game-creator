import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 20

Title "Nonempty Product"

Introduction "
# Integrating Nonemptiness and Cartesian Products

This level combines two constructions you learned separately:
`Set.Nonempty` (Level 11) and `×ˢ` (Level 10).

**Claim**: If `s` is nonempty and `t` is nonempty, then `s ×ˢ t` is
nonempty.

The proof chains three skills:
1. **Extract** witnesses from `Set.Nonempty s` and `Set.Nonempty t`
   using `obtain` (existential unpacking)
2. **Provide** the pair `(a, b)` as a witness for `Set.Nonempty (s ×ˢ t)`
   using `use`
3. **Prove** the pair is in the product using `rw [Set.mem_prod]` and
   the individual memberships

This is mathematically obvious — if you have an element from each set,
you can form a pair — but the formal proof exercises the tools in
combination.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- The product of two nonempty sets is nonempty. -/
Statement (α : Type) (β : Type) (s : Set α) (t : Set β)
    (hs : Set.Nonempty s) (ht : Set.Nonempty t) :
    Set.Nonempty (s ×ˢ t) := by
  Hint "`hs : Set.Nonempty s` means `∃ a, a ∈ s`. Extract the witness
  with `obtain ⟨a, ha⟩ := hs`."
  obtain ⟨a, ha⟩ := hs
  Hint "Now extract the witness from `ht`: `obtain ⟨b, hb⟩ := ht`."
  obtain ⟨b, hb⟩ := ht
  Hint "You have `a ∈ s` and `b ∈ t`. The goal is
  `Set.Nonempty (s ×ˢ t)`, which means `∃ p, p ∈ s ×ˢ t`.

  Provide the pair as witness: `use (a, b)`."
  Hint (hidden := true) "`use (a, b)` then `rw [Set.mem_prod]` then
  `exact ⟨ha, hb⟩`."
  use (a, b)
  Hint "The goal is `(a, b) ∈ s ×ˢ t`. Use `rw [Set.mem_prod]` to
  convert to a conjunction."
  rw [Set.mem_prod]
  Hint "The goal is `a ∈ s ∧ b ∈ t`. You have both pieces. Close with
  `exact ⟨ha, hb⟩` or use `constructor`."
  exact ⟨ha, hb⟩

Conclusion "
You proved that the product of nonempty sets is nonempty. The proof
combined three tools:

```
obtain ⟨a, ha⟩ := hs    -- extract witness from s
obtain ⟨b, hb⟩ := ht    -- extract witness from t
use (a, b)               -- provide the pair
rw [Set.mem_prod]        -- reduce to conjunction
exact ⟨ha, hb⟩           -- close with both memberships
```

**Integration summary**: This level used `obtain` (for ∃ unpacking),
`use` (for ∃ introduction), `rw [Set.mem_prod]` (for product
membership), and anonymous constructors `⟨_, _⟩` (for conjunctions).
These are all tools from earlier in this world, now working together.

In ordinary math: \"If $a \\in s$ and $b \\in t$, then $(a, b) \\in
s \\times t$, so $s \\times t \\neq \\emptyset$.\"
"

/-- `Set.Nonempty.prod` states that the product of two nonempty sets
is nonempty. -/
TheoremDoc Set.Nonempty.prod as "Set.Nonempty.prod" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.Nonempty.prod
