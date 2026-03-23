import Game.Metadata

World "SetOpsWorld"
Level 12

Title "De Morgan's Law"

Introduction "
# De Morgan's Law for Sets

One of the most important identities in set theory is **De Morgan's law**:

$$(s \\cup t)^c = s^c \\cap t^c$$

In words: the complement of a union equals the intersection of the
complements. An element is outside `s ∪ t` if and only if it is
outside both `s` and `t`.

You already proved the `⊆` direction in Level 11 using `push_neg`.
Now you must prove the full **equality** — both directions.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔` into forward (`→`) and backward (`←`)
3. **Forward** (`→`): Given `x ∈ (s ∪ t)ᶜ`, prove `x ∈ sᶜ ∩ tᶜ`.
   Use `change` and `push_neg` as in Level 11.
4. **Backward** (`←`): Given `x ∈ sᶜ ∩ tᶜ`, prove `x ∈ (s ∪ t)ᶜ`.
   Destructure the hypothesis, introduce the union assumption,
   then case-split.

This is the longest proof in the world so far. Take it step by step —
each individual step is familiar from earlier levels.
"

/-- De Morgan's law: the complement of a union is the intersection
of the complements. -/
Statement (α : Type) (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  Hint "The goal is a set equality. Use `ext x` to reduce it to a
  membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔` into two directions."
  constructor
  -- Forward: (s ∪ t)ᶜ ⊆ sᶜ ∩ tᶜ
  · Hint "**Forward direction**: you have a complement-of-union
    membership to prove intersection-of-complements. This is the
    same as Level 10: `intro hx`, then `change` and `push_neg`."
    intro hx
    Hint "Use `change ¬(x ∈ s ∨ x ∈ t) at hx` to unwrap the
    complement-of-union, then `push_neg at hx`."
    Hint (hidden := true) "`change ¬(x ∈ s ∨ x ∈ t) at hx` then
    `push_neg at hx` then `exact hx`."
    change ¬(x ∈ s ∨ x ∈ t) at hx
    push_neg at hx
    exact hx
  -- Backward: sᶜ ∩ tᶜ ⊆ (s ∪ t)ᶜ
  · Hint "**Backward direction**: given `x ∈ sᶜ ∩ tᶜ`, prove
    `x ∈ (s ∪ t)ᶜ`. Start with `intro hx` then destructure the
    intersection hypothesis."
    intro hx
    Hint "Destructure `hx : x ∈ sᶜ ∩ tᶜ` to get the two complement
    memberships: `obtain ⟨hs, ht⟩ := hx`."
    obtain ⟨hs, ht⟩ := hx
    Hint "Now `hs : x ∈ sᶜ` (meaning `x ∉ s`) and `ht : x ∈ tᶜ`
    (meaning `x ∉ t`). The goal is `x ∈ (s ∪ t)ᶜ`, meaning
    `x ∉ s ∪ t`, meaning `x ∈ s ∪ t → False`.

    Use `intro h` to assume `x ∈ s ∪ t`, then case-split on `h`."
    Hint (hidden := true) "`intro h` then `cases h with | inl h₁ | inr h₂`.
    In each case, apply the relevant complement hypothesis to derive
    `False`."
    intro h
    Hint "Now split the union hypothesis: `cases h with | inl h₁ | inr h₂`."
    cases h with
    | inl h₁ =>
      Hint "You have `h₁ : x ∈ s` and `hs : x ∈ sᶜ` (= `x ∉ s`).
      These contradict. Use `exact hs h₁`."
      Hint (hidden := true) "`exact hs h₁` — applying `hs` (which is
      `x ∈ s → False`) to `h₁ : x ∈ s` gives `False`.

      Alternatively: `contradiction`."
      Branch
        contradiction
      exact hs h₁
    | inr h₂ =>
      Hint "You have `h₂ : x ∈ t` and `ht : x ∈ tᶜ` (= `x ∉ t`).
      Use `exact ht h₂`."
      Branch
        contradiction
      exact ht h₂

Conclusion "
You proved De Morgan's law for sets! The proof combined:

- **`ext x`** — reduce set equality to element-wise biconditional
- **`push_neg`** — convert the negated disjunction (forward direction)
- **`cases h`** — case analysis on the union hypothesis (backward direction)
- **Complement application** — `hs h₁` applies `x ∉ s` to `x ∈ s`

In ordinary math, this proof reads: \"Let $x \\in (s \\cup t)^c$. Then
$x \\notin s \\cup t$, so $x \\notin s$ and $x \\notin t$ (De Morgan),
hence $x \\in s^c \\cap t^c$. Conversely, let $x \\in s^c \\cap t^c$.
Suppose $x \\in s \\cup t$. If $x \\in s$, this contradicts $x \\in s^c$.
If $x \\in t$, this contradicts $x \\in t^c$. Either way, contradiction.\"

The library name is `Set.compl_union`. In the next level, you will
prove the dual: $(s \\cap t)^c = s^c \\cup t^c$ (`Set.compl_inter`).
"

/-- `Set.compl_union` states that the complement of a union is the
intersection of the complements: `(s ∪ t)ᶜ = sᶜ ∩ tᶜ`.

This is **De Morgan's law** for sets.

## Statement
```
Set.compl_union : (s ∪ t)ᶜ = sᶜ ∩ tᶜ
```

## Dual
`Set.compl_inter : (s ∩ t)ᶜ = sᶜ ∪ tᶜ`
-/
TheoremDoc Set.compl_union as "Set.compl_union" in "Set"

/-- `Set.compl_inter` states `(s ∩ t)ᶜ = sᶜ ∪ tᶜ` (dual De Morgan). -/
TheoremDoc Set.compl_inter as "Set.compl_inter" in "Set"

/-- `compl_inf` is the lattice version: `(a ⊓ b)ᶜ = aᶜ ⊔ bᶜ`. -/
TheoremDoc compl_inf as "compl_inf" in "Set"

/-- `compl_sup` is the lattice version of De Morgan: `(a ⊔ b)ᶜ = aᶜ ⊓ bᶜ`. -/
TheoremDoc compl_sup as "compl_sup" in "Set"

/-- `not_or` states `¬(a ∨ b) ↔ ¬a ∧ ¬b` (propositional De Morgan). -/
TheoremDoc not_or as "not_or" in "Set"

NewTheorem Set.compl_union

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.compl_union compl_sup Set.compl_inter compl_inf not_or
