import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 14

Title "Nonemptiness Converse"

Introduction "
# The Converse: Union Nonempty Implies Some Member Nonempty

In the previous level, you proved that if some member `s j` is
nonempty, then `⋃ i, s i` is nonempty. Now prove the **converse**:
if the indexed union is nonempty, then at least one member must be
nonempty.

This is a direct consequence of unpacking what `⋃ i, s i` means:
an element in the union witnesses BOTH a specific index AND membership
in that index's set — which is exactly what it means for that member
to be nonempty.

The proof chains two existential unpackings (one from `Set.Nonempty`,
one from `Set.mem_iUnion`) and then repacks the data into the goal.

**Your task**: Given that `⋃ i, s i` is nonempty, produce an index
`j` such that `s j` is nonempty.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty
TheoremTab "Set"

/-- If the indexed union is nonempty, some member is nonempty. -/
Statement (α : Type) (ι : Type) (s : ι → Set α)
    (h : Set.Nonempty (⋃ i, s i)) : ∃ j, Set.Nonempty (s j) := by
  Hint "`h : Set.Nonempty (⋃ i, s i)` means `∃ x, x ∈ ⋃ i, s i`.
  Extract the witness element with `obtain ⟨x, hx⟩ := h`."
  obtain ⟨x, hx⟩ := h
  Hint "You have `hx : x ∈ ⋃ i, s i`. Use `rw [Set.mem_iUnion] at hx`
  to convert to `∃ i, x ∈ s i`."
  rw [Set.mem_iUnion] at hx
  Hint "Now `hx : ∃ i, x ∈ s i`. Extract the index witness:
  `obtain ⟨j, hj⟩ := hx`."
  obtain ⟨j, hj⟩ := hx
  Hint "You have `j : ι` and `hj : x ∈ s j`. The goal is
  `∃ j, Set.Nonempty (s j)`. Provide `j` as the witness with `use j`,
  then provide `x` as the nonemptiness witness with `use x`."
  Hint (hidden := true) "`use j` then `use x`."
  use j
  use x

Conclusion "
You proved the converse of Level 13: if the indexed union is nonempty,
some member must be nonempty. Together, the two results say:

$$\\bigcup_i s_i \\neq \\emptyset \\;\\Longleftrightarrow\\;
\\exists\\, j,\\; s_j \\neq \\emptyset$$

The proof unpacked two nested existentials and repacked them:

```
obtain ⟨x, hx⟩ := h         -- extract element from union
rw [Set.mem_iUnion] at hx   -- convert ⋃ to ∃
obtain ⟨j, hj⟩ := hx        -- extract index from ∃
use j                        -- provide index witness
use x                        -- provide element witness
```

**The general lesson**: When you need to prove an existential, look for
data hiding inside your hypotheses. Here, the element `x` and the index
`j` were both buried inside the nonemptiness hypothesis — you just
extracted and rearranged them.

In ordinary math: \"If $\\bigcup_i s_i$ is nonempty, pick $x \\in
\\bigcup_i s_i$. Then $x \\in s_j$ for some $j$, so $s_j$ is nonempty.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
