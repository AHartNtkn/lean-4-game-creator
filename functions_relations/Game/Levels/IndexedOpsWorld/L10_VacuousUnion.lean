import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 10

Title "Vacuous Union"

Introduction "
# The Dual: Union over Nothing

In the previous level, you proved the surprising fact that intersecting
over an empty family gives `Set.univ` — because the condition
`∀ i, x ∈ s i` is vacuously true when there are no indices.

Now prove the **dual**: unioning over an empty family gives `∅`.

$$\\bigcup_{i \\in \\emptyset} s_i = \\emptyset$$

This is less surprising: if there are no sets to contribute elements,
the union is empty. The membership condition `∃ i, x ∈ s i` is false
when the index type `Empty` has no elements — you cannot produce a
witness that does not exist.

Together, these two results give the cleanest illustration of the
`∃`/`∀` duality in indexed operations:

| Operation | Over `Empty` | Reason |
|---|---|---|
| `⋂ i, s i` | `Set.univ` | `∀ i : Empty, P i` is vacuously true |
| `⋃ i, s i` | `∅` | `∃ i : Empty, P i` is impossible |

**Your task**: Prove that the union over an empty index type is `∅`.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂
NewDefinition Set.iUnion Set.iInter Empty
TheoremTab "Set"

/-- The union over an empty index type is the empty set. -/
Statement (α : Type) (s : Empty → Set α) :
    ⋃ i, s i = ∅ := by
  Hint "This is a set equality. Start with `ext x` to reduce to a
  membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔`."
  constructor
  · Hint "**Forward direction**: You have `x ∈ ⋃ i, s i` and must show
    `x ∈ ∅`. Use `rw [Set.mem_iUnion]` to unpack the union, then
    extract the witness — but the witness has type `Empty`, so it
    cannot exist!"
    Hint (hidden := true) "`intro hx` then `rw [Set.mem_iUnion] at hx`
    then `obtain ⟨i, _⟩ := hx` then `exact i.elim`."
    intro hx
    rw [Set.mem_iUnion] at hx
    Hint "Now `hx : ∃ i, x ∈ s i` where `i : Empty`. Extract the
    witness with `obtain ⟨i, _⟩ := hx`."
    obtain ⟨i, _⟩ := hx
    Hint "You have `i : Empty` — an element of the empty type. This is
    impossible, so `i.elim` closes any goal. Use `exact i.elim`."
    exact i.elim
  · Hint "**Backward direction**: You have `x ∈ ∅`, which is impossible
    — the empty set has no elements. The hypothesis is `False` in
    disguise, so `contradiction` closes the goal."
    Hint (hidden := true) "`intro hx` then `contradiction`."
    intro hx
    contradiction

Conclusion "
You proved that `⋃ i : Empty, s i = ∅` — unioning over nothing gives
nothing.

Together with Level 9, you now have the complete duality:

| Indexed operation | Over `Empty` | Logic |
|---|---|---|
| `⋂ i : Empty, s i = Set.univ` | vacuously true `∀` | no conditions to check |
| `⋃ i : Empty, s i = ∅` | impossible `∃` | no witnesses to exhibit |

This pair is the most dramatic illustration of the `∀`/`∃` duality
that runs through the entire world. Every time you see a vacuously
true universal or an impossible existential, the same principle is
at work.

In ordinary math: \"$\\bigcup_{i \\in \\emptyset} s_i = \\emptyset$
because the defining condition — there exists $i \\in \\emptyset$ with
$x \\in s_i$ — can never be satisfied.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iUnion_of_empty iUnion_of_empty
