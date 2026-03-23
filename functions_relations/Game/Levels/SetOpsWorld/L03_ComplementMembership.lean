import Game.Metadata

World "SetOpsWorld"
Level 3

Title "Complement Membership"

Introduction "
# Complement: ᶜ means ¬

The **complement** of a set `s`, written `sᶜ`, contains everything
NOT in `s`:

$$x \\in s^c \\;\\;\\Longleftrightarrow\\;\\; x \\notin s \\;\\;\\Longleftrightarrow\\;\\; \\neg\\,(x \\in s)$$

This is exactly the non-membership you already proved in Set World!
The complement notation `sᶜ` is just a way of turning non-membership
into a set: `sᶜ = {x | x ∉ s}`.

To prove `x ∈ sᶜ`, you prove `x ∉ s`, which means showing
`x ∈ s → False`. The proof shape is:
1. `intro h` — assume `x ∈ s`
2. Derive a contradiction from `h`

**Your task**: Prove that 3 is in the complement of the even numbers.
This is the same as proving `3 ∉ {n | Even n}` — which you did
in Set World. The only difference is the notation.
"

/-- 3 is not even, so it belongs to the complement of the even set. -/
Statement : (3 : ℕ) ∈ {n : ℕ | Even n}ᶜ := by
  Hint "The goal says `3 ∈ (the even set)ᶜ`, which means `3 ∉ (the even set)`,
  which means `Even 3 → False`. Use `intro h` to assume `Even 3`."
  Hint (hidden := true) "After `intro h`, you have `h : Even 3` which
  means `∃ r, 3 = r + r`. Destructure with `obtain ⟨r, hr⟩ := h`,
  then `omega` finds the contradiction."
  Branch
    show ¬ Even 3
    intro h
    obtain ⟨r, hr⟩ := h
    omega
  intro h
  Hint "`h` says `Even 3`, meaning there exists `r` with `3 = r + r`.
  Destructure with `obtain ⟨r, hr⟩ := h`."
  obtain ⟨r, hr⟩ := h
  Hint "`hr : 3 = r + r` has no natural number solution. `omega`
  derives the contradiction."
  omega

Conclusion "
You proved `3 ∈ {n | Even n}ᶜ` using the exact same technique as
proving `3 ∉ {n | Even n}` from Set World. That is the point:

**`x ∈ sᶜ` and `x ∉ s` are the same statement.**

The complement notation `ᶜ` (typed `\\compl` or `\\^c`) lets you treat
non-membership as a set. This is useful because you can now apply
set operations to complements — for example, `sᶜ ∩ tᶜ` is the set
of elements in neither `s` nor `t`.

| Operation | Logic | Proof tactic |
|---|---|---|
| `∪` (union) | `∨` (or) | `left` / `right` |
| `∩` (intersection) | `∧` (and) | `constructor` |
| `ᶜ` (complement) | `¬` (not) | `intro h` then contradiction |

**Common confusion**: Complement is not difference. `sᶜ` contains
everything outside `s` (relative to the whole type), while `s \\ t`
contains elements in `s` but not `t`. You will see set difference
in the next level.
"

/-- `sᶜ` (typed `\\compl` or `\\^c`) is the **complement** of set `s`.

An element belongs to `sᶜ` if it does NOT belong to `s`:
$$x \\in s^c \\iff x \\notin s \\iff \\neg\\,(x \\in s)$$

## Proof strategies

**To prove** `x ∈ sᶜ`:
- `intro h` (assume `x ∈ s`), then derive contradiction

**Given** `h : x ∈ sᶜ`:
- `h` is a function from `x ∈ s` to `False`
- Apply it: `exact h hx` if `hx : x ∈ s`

## Example
`3 ∈ {n | Even n}ᶜ` reduces to `¬ Even 3`.

## Warning
`sᶜ` is the complement relative to the entire type `α`, not relative
to some ambient set. `sᶜ = {x : α | x ∉ s}`.
-/
DefinitionDoc Set.compl as "Set.compl"

NewDefinition Set.compl

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
