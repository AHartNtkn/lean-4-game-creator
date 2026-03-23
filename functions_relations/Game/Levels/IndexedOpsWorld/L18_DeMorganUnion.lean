import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 18

Title "De Morgan for Indexed Unions"

Introduction "
# De Morgan's Law for Indexed Unions

In Set Operations World, you proved De Morgan's law for binary unions:
$(s \\cup t)^c = s^c \\cap t^c$. Now prove the indexed generalization:

$$(\\bigcup_i s_i)^c = \\bigcap_i (s_i)^c$$

In words: an element is outside the union of a family if and only if
it is outside every member of the family. This is the set-theoretic
version of the logical equivalence $\\neg(\\exists i,\\, P(i))
\\Longleftrightarrow \\forall i,\\, \\neg P(i)$.

This is the first level that requires BOTH `mem_iUnion` and
`mem_iInter` in the same proof — one for each side of the equation.

**Proof plan**: Use `ext` and `constructor` as usual. In each
direction, the complement turns `∈` into `∉` (an implication to
`False`), and you bridge between `⋃` and `⋂` through the
negation of quantifiers.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- De Morgan's law: the complement of an indexed union is the
indexed intersection of complements. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) :
    (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ := by
  Hint "Start with `ext x` to reduce to a membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔` into forward and backward
  directions."
  constructor
  -- Forward: x ∈ (⋃ i, s i)ᶜ → x ∈ ⋂ i, (s i)ᶜ
  · Hint "**Forward direction**: You have `x ∈ (⋃ i, s i)ᶜ`, which
    means `x ∉ ⋃ i, s i`. You must show `x ∈ ⋂ i, (s i)ᶜ`, which
    means `∀ i, x ∉ s i`.

    If you learned `push_neg` in Set Operations World, you might think
    of using it here — but it is disabled in this level so you can see
    exactly what `push_neg` does under the hood for indexed operations.

    Start with `intro hx` to assume the complement membership."
    intro hx
    Hint "Use `rw [Set.mem_iInter]` to convert the goal to
    `∀ i, x ∈ (s i)ᶜ`."
    rw [Set.mem_iInter]
    Hint "Use `intro i` to introduce the index."
    intro i
    Hint "The goal is `x ∈ (s i)ᶜ`, which means `x ∉ s i`, i.e.,
    `x ∈ s i → False`. Use `intro hsi` to assume `x ∈ s i` and
    derive a contradiction."
    Hint (hidden := true) "`intro hsi` then `apply hx` then
    `rw [Set.mem_iUnion]` then `exact ⟨i, hsi⟩`."
    intro hsi
    Hint "You have `hx : x ∈ (⋃ i, s i)ᶜ` (i.e., `x ∉ ⋃ i, s i`)
    and `hsi : x ∈ s i`. Derive a contradiction by showing `x`
    IS in the union: `apply hx`."
    apply hx
    Hint "The goal is `x ∈ ⋃ i, s i`. Rewrite and provide the witness."
    rw [Set.mem_iUnion]
    exact ⟨i, hsi⟩
  -- Backward: x ∈ ⋂ i, (s i)ᶜ → x ∈ (⋃ i, s i)ᶜ
  · Hint "**Backward direction**: You have `x ∈ ⋂ i, (s i)ᶜ`, which
    means `∀ i, x ∉ s i`. You must show `x ∈ (⋃ i, s i)ᶜ`, which
    means `x ∉ ⋃ i, s i`.

    Start with `intro hx`."
    intro hx
    Hint "The goal is `x ∈ (⋃ i, s i)ᶜ`, i.e., `x ∉ ⋃ i, s i`.
    Use `intro hu` to assume `x ∈ ⋃ i, s i` and derive a contradiction."
    intro hu
    Hint "Unpack the union: `rw [Set.mem_iUnion] at hu` to get
    `∃ i, x ∈ s i`."
    Hint (hidden := true) "`rw [Set.mem_iUnion] at hu` then
    `obtain ⟨i, hsi⟩ := hu` then `rw [Set.mem_iInter] at hx` then
    `exact hx i hsi`."
    rw [Set.mem_iUnion] at hu
    Hint "Extract the witness: `obtain ⟨i, hsi⟩ := hu`."
    obtain ⟨i, hsi⟩ := hu
    Hint "You have `hsi : x ∈ s i`. Now use `hx` to get the
    contradiction. Rewrite `hx` with `rw [Set.mem_iInter] at hx`."
    rw [Set.mem_iInter] at hx
    Hint "Now `hx : ∀ i, x ∈ (s i)ᶜ`. Specialize to `i`:
    `hx i` gives `x ∈ (s i)ᶜ`, which means `x ∉ s i`.
    But `hsi : x ∈ s i` — contradiction. Close with `exact hx i hsi`."
    exact hx i hsi

Conclusion "
You proved De Morgan's law for indexed unions:
$(\\bigcup_i s_i)^c = \\bigcap_i (s_i)^c$

This is the first proof where you used BOTH `mem_iUnion` and
`mem_iInter` together. The key insight is how negation swaps
quantifiers:

| Statement | Negation |
|---|---|
| $\\exists i,\\; x \\in s_i$ | $\\forall i,\\; x \\notin s_i$ |
| $x \\in \\bigcup_i s_i$ | $x \\in \\bigcap_i (s_i)^c$ |

**The logical core**: De Morgan for sets is just De Morgan for
quantifiers in disguise: $\\neg(\\exists i,\\, P(i)) \\iff \\forall i,\\,
\\neg P(i)$. The complement `ᶜ` is `¬`, the union `⋃` is `∃`,
and the intersection `⋂` is `∀`.

In ordinary math: \"$x \\notin \\bigcup_i s_i$ means there is no $i$
with $x \\in s_i$, which means for every $i$, $x \\notin s_i$, which
means $x \\in \\bigcap_i s_i^c$.\"

**Up next**: The dual De Morgan law $(\\bigcap_i s_i)^c = \\bigcup_i (s_i)^c$
— the harder direction, where you will need classical reasoning.
"

/-- `Set.compl_iUnion` states `(⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ`. -/
TheoremDoc Set.compl_iUnion as "Set.compl_iUnion" in "Set"

/-- `Set.compl_iInter` states `(⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ`. -/
TheoremDoc Set.compl_iInter as "Set.compl_iInter" in "Set"

/-- `compl_iSup` is the lattice version of `Set.compl_iUnion`. -/
TheoremDoc compl_iSup as "compl_iSup" in "Set"

/-- `compl_iInf` is the lattice version of `Set.compl_iInter`. -/
TheoremDoc compl_iInf as "compl_iInf" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith push_neg
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_iUnion Set.compl_iInter compl_iSup compl_iInf
