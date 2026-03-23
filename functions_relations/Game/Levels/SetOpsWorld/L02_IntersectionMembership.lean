import Game.Metadata

World "SetOpsWorld"
Level 2

Title "Intersection Membership"

Introduction "
# Intersection: ∩ means ∧

The **intersection** of two sets `s ∩ t` contains elements that belong
to **both** `s` and `t`:

$$x \\in s \\cap t \\;\\;\\Longleftrightarrow\\;\\; x \\in s \\;\\land\\; x \\in t$$

Intersection IS conjunction. To prove `x ∈ s ∩ t`, you prove both
`x ∈ s` AND `x ∈ t` — and you already know the tactic for that:
`constructor` splits a conjunction into two goals.

**Your task**: Prove that 4 is in the intersection. You need both
`Even 4` and `4 < 10`.

**Proof plan**:
1. `constructor` — split the conjunction into two goals
2. First goal: prove `Even 4` using `use 2`
3. Second goal: prove `4 < 10` using `omega`
"

/-- 4 is both even and less than 10. -/
Statement : (4 : ℕ) ∈ ({n : ℕ | Even n} ∩ {n | n < 10}) := by
  Hint "The goal is an intersection membership, which means a conjunction.
  Use `constructor` to split it into two goals: `Even 4` and `4 < 10`."
  Branch
    show Even 4 ∧ 4 < 10
    Hint "Now you can see the `∧` explicitly. Use `constructor` to split."
    constructor
    · use 2
    · omega
  constructor
  -- First goal: Even 4
  · Hint "Prove `Even 4`. Recall that `Even n` means there exists `r`
    with `n = r + r`. Provide the witness: `use 2`."
    Hint (hidden := true) "`use 2` sets the goal to `4 = 2 + 2`,
    which `rfl` closes (or it closes automatically)."
    use 2
  -- Second goal: 4 < 10
  · Hint "Prove that 4 is less than 10. Use `show 4 < 10` to unfold
    the set-builder notation, then `omega`."
    Hint (hidden := true) "`show 4 < 10` then `omega`."
    show 4 < 10
    omega

Conclusion "
You proved intersection membership using `constructor` — the same
tactic you use for any conjunction.

| Operation | Logic | Proof tactic |
|---|---|---|
| `∪` (union) | `∨` (or) | `left` / `right` |
| `∩` (intersection) | `∧` (and) | `constructor` |

**Extracting from intersections**: If you have a hypothesis
`h : x ∈ s ∩ t`, you can extract the components just like a
conjunction:
- `h.1 : x ∈ s` (left component)
- `h.2 : x ∈ t` (right component)
- `obtain ⟨hs, ht⟩ := h` destructures into both components

You will use extraction in later levels when an intersection
hypothesis appears on the left side of an implication.
"

/-- `s ∩ t` (typed `\\cap` or `\\inter`) is the **intersection** of
sets `s` and `t`.

An element belongs to `s ∩ t` if it belongs to **both** `s` and `t`:
$$x \\in s \\cap t \\iff x \\in s \\land x \\in t$$

## Proof strategies

**To prove** `x ∈ s ∩ t`:
- `constructor` then prove `x ∈ s` and `x ∈ t` separately

**Given** `h : x ∈ s ∩ t`:
- `h.1 : x ∈ s` and `h.2 : x ∈ t` (dot projection)
- `obtain ⟨hs, ht⟩ := h` (destructuring)

## Warning
Unlike union, you must prove **both** components — you cannot
choose just one.
-/
DefinitionDoc Set.inter as "Set.inter"

NewDefinition Set.inter

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
