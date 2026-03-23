import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 19

Title "De Morgan for Indexed Intersections"

Introduction "
# De Morgan's Law for Indexed Intersections

In the previous level, you proved that $(\\bigcup_i s_i)^c =
\\bigcap_i (s_i)^c$, which is the set version of
$\\neg\\exists \\Leftrightarrow \\forall\\neg$.

Now prove the **dual**: $(\\bigcap_i s_i)^c = \\bigcup_i (s_i)^c$,
which is the set version of $\\neg\\forall \\Leftrightarrow \\exists\\neg$.

**Why this is harder**: The previous direction ($\\neg\\exists \\to
\\forall\\neg$) is constructive — if no witness exists, you can show the
property holds for all indices directly. But the current direction
($\\neg\\forall \\to \\exists\\neg$) is **classical**: knowing that
\"not all sets contain x\" does not directly hand you a specific set
that excludes x. You need proof by contradiction (`by_contra`) to find
the witness.

**Proof plan for the forward direction** ($x \\notin \\bigcap_i s_i \\to
x \\in \\bigcup_i (s_i)^c$):
1. Assume the goal is false (`by_contra`)
2. Show that this forces `x ∈ ⋂ i, s i` — contradicting the hypothesis
3. To show `x ∈ s i` for arbitrary `i`, assume `x ∉ s i` and derive
   a contradiction with the by_contra hypothesis

The backward direction is constructive and follows the same pattern as
the previous level.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- De Morgan's law: the complement of an indexed intersection is the
indexed union of complements. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) :
    (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ := by
  Hint "Start with `ext x` to reduce to a membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔`."
  constructor
  -- Forward: x ∈ (⋂ i, s i)ᶜ → x ∈ ⋃ i, (s i)ᶜ
  · Hint "**Forward direction (the classical one)**: You will assume
    `x ∈ (⋂ i, s i)ᶜ`, meaning `x ∉ ⋂ i, s i`. You must produce
    a specific index `i` with `x ∉ s i`. This requires `by_contra`.

    Start with `intro hx`."
    intro hx
    Hint "Rewrite the goal: `rw [Set.mem_iUnion]` to get
    `∃ i, x ∈ (s i)ᶜ`."
    rw [Set.mem_iUnion]
    Hint "The goal is `∃ i, x ∈ (s i)ᶜ`. You cannot directly name
    the witness — you need proof by contradiction.

    Use `by_contra h` to assume `¬ ∃ i, x ∈ (s i)ᶜ` and derive `False`."
    Hint (hidden := true) "`by_contra h` then `apply hx` then
    `rw [Set.mem_iInter]` then `intro i` then `by_contra hni` then
    `exact h ⟨i, hni⟩`."
    by_contra h
    Hint "Now `h : ¬ ∃ i, x ∈ (s i)ᶜ` and the goal is `False`.
    You also have `hx : x ∈ (⋂ i, s i)ᶜ`, meaning `x ∉ ⋂ i, s i`.

    To reach `False`, show that `x ∈ ⋂ i, s i` after all — contradicting
    `hx`. Use `apply hx` to change the goal to `x ∈ ⋂ i, s i`."
    apply hx
    Hint "The goal is `x ∈ ⋂ i, s i`. Rewrite to a universal:
    `rw [Set.mem_iInter]`."
    rw [Set.mem_iInter]
    Hint "The goal is `∀ i, x ∈ s i`. Use `intro i` to introduce
    the index."
    intro i
    Hint "The goal is `x ∈ s i`. You cannot prove this directly, but
    you can assume the opposite and derive a contradiction.

    Use `by_contra hni` to assume `x ∉ s i`."
    by_contra hni
    Hint "Now `hni : x ∉ s i` (which is the same as `x ∈ (s i)ᶜ`).
    You also have `h : ¬ ∃ i, x ∈ (s i)ᶜ`. But `⟨i, hni⟩` IS a
    witness for `∃ i, x ∈ (s i)ᶜ` — contradiction!

    Close with `exact h ⟨i, hni⟩`."
    exact h ⟨i, hni⟩
  -- Backward: x ∈ ⋃ i, (s i)ᶜ → x ∈ (⋂ i, s i)ᶜ
  · Hint "**Backward direction (constructive)**: You have a specific
    index where `x` is missing. This directly prevents `x` from being
    in the full intersection.

    Start with `intro hx`."
    intro hx
    Hint "Unpack the union: `rw [Set.mem_iUnion] at hx`."
    Hint (hidden := true) "`rw [Set.mem_iUnion] at hx` then
    `obtain ⟨i, hsi⟩ := hx` then `intro hinter` then
    `rw [Set.mem_iInter] at hinter` then `exact hsi (hinter i)`."
    rw [Set.mem_iUnion] at hx
    Hint "Extract the witness: `obtain ⟨i, hsi⟩ := hx`."
    obtain ⟨i, hsi⟩ := hx
    Hint "You have `hsi : x ∈ (s i)ᶜ` (i.e., `x ∉ s i`). The goal is
    `x ∈ (⋂ i, s i)ᶜ` (i.e., `x ∉ ⋂ i, s i`). Use `intro hinter`
    to assume `x ∈ ⋂ i, s i` and derive a contradiction."
    intro hinter
    Hint "Rewrite `hinter`: `rw [Set.mem_iInter] at hinter`."
    rw [Set.mem_iInter] at hinter
    Hint "Now `hinter : ∀ i, x ∈ s i`. But `hsi : x ∉ s i`.
    Specialize `hinter` to `i` and apply `hsi`: `exact hsi (hinter i)`."
    exact hsi (hinter i)

Conclusion "
You proved the dual De Morgan law for indexed intersections:
$(\\bigcap_i s_i)^c = \\bigcup_i (s_i)^c$

The two De Morgan laws together:

| Law | Set form | Quantifier form |
|---|---|---|
| Level 18 | $(\\bigcup_i s_i)^c = \\bigcap_i (s_i)^c$ | $\\neg\\exists \\iff \\forall\\neg$ |
| This level | $(\\bigcap_i s_i)^c = \\bigcup_i (s_i)^c$ | $\\neg\\forall \\iff \\exists\\neg$ |

**Why one direction needed `by_contra`**: The forward direction of this
level required finding a specific index `i` where `x ∉ s i`, given
only that `x` is not in ALL of them. You cannot constructively extract
a witness from a negated universal — you need classical reasoning
(proof by contradiction) to do it. This is the fundamental asymmetry
between `∃` and `∀` under negation.

In Set Operations World, `push_neg` handled this automatically. Here
you saw what `push_neg` does under the hood: a double `by_contra` that
converts `¬∀` into `∃¬`.

**The double-contradiction extraction**: This proof pattern —
assume the goal is false with `by_contra`, then show the original
hypothesis is contradicted by using a SECOND `by_contra` inside a
universal — is a reusable strategy for `¬∀ → ∃¬` arguments. Whenever
you need to extract a witness from a negated universal, reach for this
double-contradiction pattern. You will encounter it again in topology
and analysis.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith push_neg
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_iUnion Set.compl_iInter compl_iSup compl_iInf
