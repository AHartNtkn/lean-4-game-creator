import Game.Metadata

World "PsetSets"
Level 10

Title "Indexed Union and Range"

TheoremTab "Set"

Introduction "
# Problem Set: Level 10

This level practices **`Set.range`**, which you first saw in
Indexed Operations World.

Recall: for a function `f : α → β`, the **range** of `f` is the
set of all output values:

$$\\text{range}(f) = \\{y \\mid \\exists\\, x,\\; f(x) = y\\}$$

In Lean, `Set.range f = {y | ∃ x, f x = y}`. The rewrite rule
`Set.mem_range` converts between `y ∈ Set.range f` and `∃ x, f x = y`.

**Your task**: Prove that the indexed union of singletons equals the
range:

$$\\bigcup_i \\{x \\mid x = f(i)\\} = \\text{range}(f)$$

This is natural: the union of all \"just `f(i)`\" sets IS the set of
all values `f` takes. The proof uses `Set.mem_iUnion` on the left and
`Set.mem_range` on the right.
"



/-- The indexed union of singleton fibers equals the range. -/
Statement (α : Type) (β : Type) (f : α → β) :
    ⋃ i, {x | x = f i} = Set.range f := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ ⋃ i, {x | x = f i} → x ∈ Set.range f
  · Hint "Unpack the indexed union with `rw [Set.mem_iUnion]`, extract
    the witness, then convert the goal with `rw [Set.mem_range]`."
    intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    Hint "You have `hi : x = f i`. The goal is `x ∈ Set.range f`.
    Use `rw [Set.mem_range]` to convert to `∃ a, f a = x`."
    Hint (hidden := true) "Key move: `rw [Set.mem_range]` then provide
    the witness `i` with the equality reversed."
    rw [Set.mem_range]
    exact ⟨i, hi.symm⟩
  -- Backward: x ∈ Set.range f → x ∈ ⋃ i, {x | x = f i}
  · Hint "Unpack the range with `rw [Set.mem_range]`, extract the
    witness, then convert the goal with `rw [Set.mem_iUnion]`."
    intro hx
    rw [Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    Hint "You have `hi : f i = x`. Use `rw [Set.mem_iUnion]` and
    provide the witness `i`. Then `hi.symm` gives `x = f i`."
    Hint (hidden := true) "Key move: `rw [Set.mem_iUnion]` then
    provide the witness with the equality reversed."
    rw [Set.mem_iUnion]
    exact ⟨i, hi.symm⟩

Conclusion "
You proved that the indexed union of singleton fibers equals the range:
$\\bigcup_i \\{x \\mid x = f(i)\\} = \\text{range}(f)$

The proof was symmetric: each direction used:
1. Rewrite to convert set membership to an existential
2. Extract the witness index
3. Provide the witness with `.symm` to flip the equality direction

**Recall**: `rw [Set.mem_range]` converts `y ∈ Set.range f` to
`∃ x, f x = y`. This works exactly like `rw [Set.mem_iUnion]` — it
bridges between set notation and quantifier logic.

**Looking ahead**: `Set.range f` is the set of all outputs of `f`.
In the upcoming Image and Preimage worlds, you will study:
- **Preimage**: `f ⁻¹' t = {x | f x ∈ t}` — elements that map INTO `t`
- **Image**: `f '' s = {y | ∃ x ∈ s, f x = y}` — outputs from `s`
- `Set.range f = f '' Set.univ` — the range is the image of everything

**Think ahead**: You just proved that `⋃ i, {x | x = f i} = Set.range f`.
The image `f '' s` collects all outputs from inputs in `s`. What do you
think the relationship between `f '' Set.univ` and `Set.range f` is?
Why might that be true?
"

/-- `Set.iUnion_singleton_eq_range` states `⋃ x, {f x} = Set.range f`. -/
TheoremDoc Set.iUnion_singleton_eq_range as "Set.iUnion_singleton_eq_range" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iUnion_singleton_eq_range
