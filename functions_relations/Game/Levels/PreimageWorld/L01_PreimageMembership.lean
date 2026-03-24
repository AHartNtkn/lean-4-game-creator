import Game.Metadata

World "PreimageWorld"
Level 1

Title "What is a Preimage?"

TheoremTab "Set"

Introduction "
# Preimages: Pulling Sets Back Through Functions

You have mastered sets, subsets, and set operations. Now you will see
how **functions** interact with sets.

Given a function `f : α → β` and a set `t : Set β` (a set of
**outputs**), the **preimage** of `t` under `f` is the set of all
**inputs** whose output lands in `t`:

$$f^{-1}(t) = \\{x \\mid f(x) \\in t\\}$$

In Lean, the preimage is written `f ⁻¹' t` (type `\\-1'`). Its
definition is:

$$x \\in f\\;⁻¹' t \\;\\;\\Longleftrightarrow\\;\\; f(x) \\in t$$

This is `Set.mem_preimage`. Notice: the definition is just
**\"apply `f`, then check membership.\"** There is no existential,
no witness — just function application.

**Your task**: Prove that 3 is in the preimage of `{n | n < 5}`
under the function `n ↦ n + 1`. This means showing that
`3 + 1 < 5`, i.e., `4 < 5`.

**Proof plan**:
1. `show 3 + 1 < 5` — unfold the preimage membership to arithmetic
2. `omega` — close the arithmetic goal
"

/-- 3 is in the preimage because applying the function gives a value in the target set. -/
Statement : (3 : ℕ) ∈ (fun n : ℕ => n + 1) ⁻¹' {n | n < 5} := by
  Hint "The goal says `3 ∈ (fun n => n + 1) ⁻¹' ...`. By the definition
  of preimage, this means `(fun n => n + 1) 3 ∈ ...`, which is
  `3 + 1 < 5`. Use `show 3 + 1 < 5` to make this explicit."
  Hint (hidden := true) "`show 3 + 1 < 5` then `omega`."
  show 3 + 1 < 5
  omega

Conclusion "
You proved your first preimage membership! The proof was:

1. **Unfold**: `3 ∈ f ⁻¹' t` means `f 3 ∈ t`, which is `3 + 1 < 5`
2. **Compute**: `4 < 5` ✓

The key insight: **preimage membership is just function application
followed by a membership check.** There is no construction, no witness,
no existential — just \"apply `f` and see if the result is in `t`.\"

Compare with set-builder membership from Set World: `3 ∈ {n | n < 5}`
means `3 < 5`. Preimage membership `3 ∈ f ⁻¹' {n | n < 5}` means
`f 3 < 5` — one extra function application, same idea.

The notation `f ⁻¹' t` is typed `\\-1'` (with the apostrophe).
The apostrophe distinguishes the **set-valued** preimage from the
function inverse `f⁻¹`. Lean uses `⁻¹'` for sets and `⁻¹` for
function inverses.
"

/-- `Set.preimage f t`, written `f ⁻¹' t`, is the **preimage** of `t`
under `f` — the set of all inputs whose output is in `t`:

$$f^{-1}(t) = \\{x \\mid f(x) \\in t\\}$$

## Membership rule
`x ∈ f ⁻¹' t ↔ f x ∈ t` (this is `Set.mem_preimage`)

## Syntax
```
f ⁻¹' t      -- preimage of t under f (type \-1')
```

## When to use it
When you want to talk about which inputs of `f` produce outputs in `t`.

## Example
If `f n = n + 1`, then `f ⁻¹' {n | n < 5} = {n | n + 1 < 5} = {0, 1, 2, 3}`.

## Warning
`f ⁻¹' t` is a set of INPUTS (type `Set α`), not outputs. Do not
confuse with `f '' s` (image), which is a set of OUTPUTS.
-/
DefinitionDoc Set.preimage as "Set.preimage"

/-- `Set.mem_preimage` states `x ∈ f ⁻¹' s ↔ f x ∈ s` — membership
in a preimage means the function value is in the target set.

## Syntax
```
rw [Set.mem_preimage]         -- on the goal
rw [Set.mem_preimage] at h    -- on a hypothesis
```

## When to use it
When you need to convert between `x ∈ f ⁻¹' s` and `f x ∈ s`.
Often Lean unfolds this automatically (since preimage is defined
as `{x | f x ∈ s}`), but `rw [Set.mem_preimage]` is useful when
the definitional unfolding does not fire or when you want to make
the conversion explicit.

## Example
```
-- h : x ∈ f ⁻¹' s
rw [Set.mem_preimage] at h
-- h : f x ∈ s
```
-/
TheoremDoc Set.mem_preimage as "Set.mem_preimage" in "Set"

NewDefinition Set.preimage
NewTheorem Set.mem_preimage

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
