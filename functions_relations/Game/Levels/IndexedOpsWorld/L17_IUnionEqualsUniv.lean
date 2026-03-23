import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 17

Title "Indexed Union Equals Univ"

Introduction "
# Indexed Union Covers Everything

When a family of sets partitions the natural numbers, their indexed
union should be the entire universe. This level combines two tools
you have practiced separately:

- `ext` to reduce a set equality to membership (from Subset World)
- `Set.mem_iUnion` to handle the indexed union (from this world)

**Your task**: The sets `{n | n % 3 = k}` for `k ∈ Fin 3` partition
the natural numbers by remainder mod 3. Prove that their union is
`Set.univ` — every natural number has *some* remainder mod 3.

**About `Fin` construction**: The index type here is `Fin 3`. To create
a `Fin 3` value from a natural number `n` known to satisfy `n < 3`,
write `⟨n, proof⟩`. For example, `⟨x % 3, by omega⟩` creates a valid
`Fin 3` value because `x % 3 < 3` always holds. This angle-bracket
constructor packages a value with its proof of validity.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔`
3. **Forward** (`→`): anything in a union is in `Set.univ` (trivially)
4. **Backward** (`←`): given `x`, find its remainder class
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- The remainder classes mod 3 cover all natural numbers. -/
Statement : ⋃ k : Fin 3, {n : ℕ | n % 3 = k.val} = Set.univ := by
  Hint "This is a set equality. Start with `ext x` to reduce to
  a membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔` into forward and backward
  directions."
  constructor
  -- Forward: membership in the union implies membership in univ
  · Hint "The forward direction is trivial: everything is in `Set.univ`.
    Introduce the hypothesis and close with `exact Set.mem_univ x`.

    Note: `trivial` is disabled in this course, so it cannot close this
    for you. The explicit tool is `Set.mem_univ x`, which proves
    `x ∈ Set.univ` for any `x`."
    Hint (hidden := true) "`intro _` then `exact Set.mem_univ x`."
    intro _
    exact Set.mem_univ x
  -- Backward: membership in univ implies membership in the union
  · Hint "The backward direction is the interesting one. You need to
    show `x ∈ ⋃ k, ...`. Start by introducing the (trivial) hypothesis,
    then use `rw [Set.mem_iUnion]` to convert to an existential."
    intro _
    Hint "Use `rw [Set.mem_iUnion]` to convert the goal to
    `∃ k : Fin 3, x ∈ ...`."
    rw [Set.mem_iUnion]
    Hint "You need a `k : Fin 3` such that `x % 3 = k.val`. The
    natural witness is `x % 3` itself (which is always less than 3).

    Use `use ⟨x % 3, by omega⟩` to provide this witness."
    Hint (hidden := true) "`use ⟨x % 3, by omega⟩` provides the witness.
    The remaining goal is that `x % 3` equals the value of the
    witness — close it with `rfl`."
    use ⟨x % 3, by omega⟩
    rfl

Conclusion "
You proved that the remainder classes mod 3 cover everything. The proof
combined `ext` (from Subset World) with `mem_iUnion` (from this world):

```
ext x                         -- set equality → membership ↔
constructor
· intro _                     -- forward: trivial (Set.mem_univ)
  exact Set.mem_univ x
· intro _                     -- backward: find the remainder class
  rw [Set.mem_iUnion]
  use ⟨x % 3, by omega⟩      -- witness: x's own remainder
```

**The reusable recipe**: To prove `⋃ i, s i = Set.univ`, use `ext`
to reduce to membership, then for the backward direction, provide a
witness index that covers the given element. The forward direction
is always trivial (everything is in `Set.univ`).

**Mathematical content**: The remainder classes $\\{n : n \\bmod 3 = k\\}$
for $k = 0, 1, 2$ form a **partition** of $\\mathbb{N}$. A partition
has two properties:

1. **Covers everything**: $\\bigcup_k S_k = \\text{univ}$ — you just proved this.
2. **Pairwise disjoint**: $S_i \\cap S_j = \\emptyset$ for $i \\neq j$ — you did NOT prove this.

You showed the union covers everything, but a partition also requires
that the pieces don't overlap. You will prove disjointness properties
later when we study partitions and equivalence relations.
"

/-- `Set.eq_univ_iff_forall` states `s = Set.univ ↔ ∀ x, x ∈ s`. -/
TheoremDoc Set.eq_univ_iff_forall as "Set.eq_univ_iff_forall" in "Set"

/-- `Set.iUnion_eq_univ_iff` states
`⋃ i, f i = Set.univ ↔ ∀ x, ∃ i, x ∈ f i`. -/
TheoremDoc Set.iUnion_eq_univ_iff as "Set.iUnion_eq_univ_iff" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith fin_cases
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.eq_univ_iff_forall Set.iUnion_eq_univ_iff
