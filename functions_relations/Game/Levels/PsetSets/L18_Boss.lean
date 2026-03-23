import Game.Metadata

World "PsetSets"
Level 18

Title "Boss: De Morgan for Indexed Unions"

TheoremTab "Set"

Introduction "
# Boss: De Morgan's Law for Indexed Unions

Prove the indexed De Morgan law:

$$(\\bigcup_i s_i)^c = \\bigcap_i (s_i)^c$$

In words: an element is outside the union of a family if and only if
it is outside every member of the family.

You proved this in Indexed Operations World — but with `push_neg`
disabled. Now `push_neg` is available, and it transforms the proof.

**Skills required** (all from Worlds 1–4):
- `ext` + `constructor` for set equality (Subset World)
- `change` to expose logical structure under complement notation (Set World)
- `rw [Set.mem_iUnion]` and `rw [Set.mem_iInter]` (Indexed Ops World)
- `push_neg` on hypothesis AND on goal (Set Ops World)
- Complement reasoning throughout

**Proof strategy**: In each direction, use `change` to expose the
negation hidden in complement notation. Then `rw` to convert indexed
membership to a quantifier. Then `push_neg` to swap the quantifier
through the negation.
"

/-- De Morgan's law: the complement of an indexed union is the
indexed intersection of complements. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) :
    (⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ (⋃ i, s i)ᶜ → x ∈ ⋂ i, (s i)ᶜ
  · Hint "**Forward direction**: `x ∈ (⋃ i, s i)ᶜ` means `x ∉ ⋃ i, s i`.
    Use `change` to expose the negation, then `rw` to convert the union
    to an existential, then `push_neg` to swap the quantifier."
    intro hx
    Hint "Use `change ¬(x ∈ ⋃ i, s i) at hx` to expose the negation
    hidden under complement notation. Then `rw [Set.mem_iUnion] at hx`
    converts to `¬(∃ i, x ∈ s i)`."
    Hint (hidden := true) "Key sequence: `change ... at hx` then
    `rw [Set.mem_iUnion] at hx` then `push_neg at hx` then
    `rw [Set.mem_iInter]` then `intro i` then `exact hx i`."
    change ¬(x ∈ ⋃ i, s i) at hx
    Hint "Now `hx : ¬(x ∈ ⋃ i, s i)`. Use `rw [Set.mem_iUnion] at hx`
    to convert the union to an existential."
    rw [Set.mem_iUnion] at hx
    Hint "Now `hx : ¬(∃ i, x ∈ s i)`. Use `push_neg at hx` to convert
    `¬∃` to `∀¬`: this gives `∀ i, x ∉ s i`."
    push_neg at hx
    Hint "Now `hx : ∀ i, x ∉ s i`. The goal is `x ∈ ⋂ i, (s i)ᶜ`.
    Use `rw [Set.mem_iInter]` to convert to `∀ i, x ∈ (s i)ᶜ`."
    rw [Set.mem_iInter]
    Hint "The goal is `∀ i, x ∈ (s i)ᶜ`. Since `x ∈ (s i)ᶜ` is
    definitionally `x ∉ s i`, and `hx : ∀ i, x ∉ s i`, use
    `intro i` then `exact hx i`."
    intro i
    exact hx i
  -- Backward: x ∈ ⋂ i, (s i)ᶜ → x ∈ (⋃ i, s i)ᶜ
  · Hint "**Backward direction**: `x ∈ ⋂ i, (s i)ᶜ` means `∀ i, x ∉ s i`.
    Use `rw [Set.mem_iInter] at hx` to extract this. Then work on the goal:
    use `change` to expose the negation, `rw` to convert the union, and
    `push_neg` to finish."
    intro hx
    Hint "Use `rw [Set.mem_iInter] at hx` to convert the indexed
    intersection to a universal statement."
    rw [Set.mem_iInter] at hx
    Hint "Now `hx : ∀ i, x ∈ (s i)ᶜ`. The goal is `x ∈ (⋃ i, s i)ᶜ`.
    Use `change ¬(x ∈ ⋃ i, s i)` to expose the negation in the goal."
    Hint (hidden := true) "Key sequence: `change ¬(x ∈ ⋃ i, s i)` then
    `rw [Set.mem_iUnion]` then `push_neg` then `intro i` then
    `exact hx i`."
    change ¬(x ∈ ⋃ i, s i)
    Hint "Now the goal is `¬(x ∈ ⋃ i, s i)`. Use `rw [Set.mem_iUnion]`
    to convert to `¬(∃ i, x ∈ s i)`."
    rw [Set.mem_iUnion]
    Hint "The goal is `¬(∃ i, x ∈ s i)`. Use `push_neg` (on the goal —
    no `at` needed!) to convert `¬∃` to `∀¬`."
    push_neg
    Hint "The goal is `∀ i, x ∉ s i`. Use `intro i` then `exact hx i`."
    intro i
    exact hx i

Conclusion "
Congratulations — you have completed the **Sets Problem Set**!

You proved De Morgan's law for indexed unions:
$(\\bigcup_i s_i)^c = \\bigcap_i (s_i)^c$

The proof was beautifully symmetric. Both directions used the same
four-step strategy:

| Step | Forward (hypothesis) | Backward (goal) |
|---|---|---|
| 1. Expose negation | `change ¬(...) at hx` | `change ¬(...)` |
| 2. Convert union | `rw [Set.mem_iUnion] at hx` | `rw [Set.mem_iUnion]` |
| 3. Swap quantifier | `push_neg at hx` | `push_neg` |
| 4. Convert intersection | `rw [Set.mem_iInter]` | `rw [Set.mem_iInter] at hx` |

**`push_neg` did the heavy lifting**: The mathematical content of
De Morgan's law is that complement swaps `∃` and `∀` — which is
exactly what `push_neg` automates. In Indexed Operations World, you
proved this manually by introducing variables and deriving
contradictions. Now `push_neg` compresses that entire argument into
one tactic call.

**Summary of the problem set**:
- Level 1: Universal set complement identity
- Level 2: Concrete type exercise on Z
- Level 3: Distributivity (abstract sets, subset direction)
- Level 4: Partition identity via antisymm + by_cases
- Level 5: Complement-difference via double negation
- Level 6: Converse complement-difference (direct proof)
- Level 7: Nested difference identity via ext + by_contra
- Level 8: Nonempty product converse
- Level 9: Indexed intersection distributes into binary intersection
- Level 10: Indexed union equals range (retrieval)
- Level 11: Powerset of intersection = intersection of powersets
- Level 12: Counterexample — powerset does not distribute over union
- Level 13: Powerset union subset — the direction that holds
- Level 14: Complement of difference via by_contra + push_neg
- Level 15: Subset characterized via set difference
- Level 16: Absorption law
- Level 17: Set difference distributes over indexed union
- Level 18 (Boss): De Morgan for indexed unions via push_neg

**The meta-principle**: Every level in this problem set reduced a
set-theoretic statement to propositional logic — then you proved the
logic. This is no coincidence. In Lean, `Set α = α → Prop`: a set IS
a predicate. So every set equation reduces to a logical equivalence.
If you can prove the logic, you can prove the set identity. This is
the single most important lesson of Phase 1.

**Looking ahead**: In the next worlds, you will apply these set-theoretic
skills to **functions**: preimages (`f ⁻¹' t`), images (`f '' s`), and
the fundamental asymmetry between them. Preimages preserve ALL set
operations; images only preserve unions. The membership-to-logic
reduction you have mastered is exactly what those proofs require.
"

/-- `Set.compl_iUnion` states `(⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ`. -/
TheoremDoc Set.compl_iUnion as "Set.compl_iUnion" in "Set"

/-- `compl_iSup` is the lattice version of `Set.compl_iUnion`. -/
TheoremDoc compl_iSup as "compl_iSup" in "Set"

/-- `Set.compl_iInter` states `(⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ`. -/
TheoremDoc Set.compl_iInter as "Set.compl_iInter" in "Set"

/-- `compl_iInf` is the lattice version of `Set.compl_iInter`. -/
TheoremDoc compl_iInf as "compl_iInf" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_iUnion Set.compl_iInter compl_iSup compl_iInf
