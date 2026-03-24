import Game.Metadata

World "ImageWorld"
Level 3

Title "The rintro Power Tool"

TheoremTab "Set"

Introduction "
# Pattern-Matching Introduction: rintro and rcases

In Level 2, the proof of the image property took four steps:
`intro hy`, `obtain ⟨x, hx, hfx⟩ := hy`, `rw [← hfx]`, then work.

Lean offers a power tool that collapses this: **`rintro`**. It combines
`intro` with deep pattern matching in a single step. The key feature
is the **`rfl` pattern**: when you write `rfl` inside the pattern,
it automatically substitutes the equation instead of naming it.

```
rintro ⟨x, hx, rfl⟩
```

For image membership `y ∈ f '' s` (which is `∃ x ∈ s, f x = y`),
this gives you:
- `x : α` -- the witness
- `hx : x ∈ s` -- the membership proof
- The equation `f x = y` is consumed by `rfl`, which replaces `y`
  with `f x` everywhere

Compare the two approaches:

| Steps | Old way | With rintro |
|---|---|---|
| 1 | `intro hy` | `rintro ⟨x, hx, rfl⟩` |
| 2 | `obtain ⟨x, hx, hfx⟩ := hy` | (done!) |
| 3 | `rw [← hfx]` | |

The **`rcases`** tactic does the same pattern matching on an existing
hypothesis: `rcases hy with ⟨x, hx, rfl⟩`.

**Your task**: Prove that if `y` is in the image of the \"triple\"
function on numbers less than 4, then `y < 12`. Use `rintro` for
a two-step proof.
"

/-- If y is 3*x for some x < 4, then y < 12. -/
Statement : ∀ y : ℕ, y ∈ (fun n : ℕ => 3 * n) '' {n | n < 4} → y < 12 := by
  Hint "Use `rintro y ⟨x, hx, rfl⟩` to introduce `y`, destructure the
  image membership, and substitute `y = 3 * x` in one step.

  After this single tactic, you will have `x : ℕ`, `hx : x < 4`,
  and the goal will be `3 * x < 12`."
  Hint (hidden := true) "`rintro y ⟨x, hx, rfl⟩` then `show 3 * x < 12`,
  `have h : x < 4 := hx`, `omega`."
  Branch
    intro y hy
    Hint "You used `intro` -- that works too! Now destructure `hy`
    with `obtain ⟨x, hx, hfx⟩ := hy` (or try `obtain ⟨x, hx, rfl⟩ := hy`
    to substitute automatically)."
    Branch
      obtain ⟨x, hx, hfx⟩ := hy
      have h1 : x < 4 := hx
      have h2 : 3 * x = y := hfx
      omega
    obtain ⟨x, hx, rfl⟩ := hy
    show 3 * x < 12
    have h : x < 4 := hx
    omega
  rintro y ⟨x, hx, rfl⟩
  Hint "The `rfl` pattern substituted `y = 3 * x`, so the goal is now
  `3 * x < 12`. Use `show 3 * x < 12` to make this explicit to Lean."
  show 3 * x < 12
  Hint "Now `hx : x ∈ ...` contains `x < 4` but `omega` cannot see through
  set membership notation. Use `have h : x < 4 := hx` to extract the
  arithmetic fact."
  have h : x < 4 := hx
  Hint (hidden := true) "`omega`"
  omega

Conclusion "
Two steps: `rintro y ⟨x, hx, rfl⟩` then `omega`. Compare with the
four-step proof from Level 2!

**How `rintro` works**:
- `rintro y` introduces `y : ℕ` (like `intro y`)
- `rintro ⟨x, hx, rfl⟩` destructures the hypothesis (like `obtain`)
- The `rfl` pattern consumes the equation `3 * x = y` and replaces
  `y` with `3 * x` everywhere

All of this happens in one tactic step.

**`rcases` -- the hypothesis version**: If you already have a hypothesis
`hy : y ∈ f '' s` in your context, use `rcases hy with ⟨x, hx, rfl⟩`
to destructure it. Same pattern syntax, different starting point:
- `rintro` introduces from the goal
- `rcases` destructures an existing hypothesis

**When to use which**:
- `rintro ⟨x, hx, rfl⟩` -- when the hypothesis is in the goal
  (e.g., subset proofs `f '' s ⊆ t`)
- `rcases h with ⟨x, hx, rfl⟩` -- when `h` is already in context
- `obtain ⟨x, hx, rfl⟩ := h` -- equivalent to `rcases` for
  non-disjunctive patterns (you already know this one!)

The `rfl` trick is invaluable for image proofs. You will use
`rintro ⟨x, hx, rfl⟩` in nearly every image-related proof from now on.

**The `show` strategy**: In this proof (and in Level 2), you used
`show 3 * x < 12` to make Lean's internal goal match the form that
`omega` can handle. This is a general technique: when `rfl` substitution
or `rintro` leaves the goal in an opaque form (e.g., function application
not yet reduced), use `show` to restate the goal in readable arithmetic
form. You will see this pattern recur whenever `omega` needs to see
through set-builder or function notation.
"

NewTactic rintro rcases

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
