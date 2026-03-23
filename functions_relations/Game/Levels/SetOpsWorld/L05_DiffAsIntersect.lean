import Game.Metadata

World "SetOpsWorld"
Level 5

Title "Difference as Intersection with Complement"

Introduction "
# s \\ t = s ∩ tᶜ

In Level 4, we noted that set difference combines intersection and
complement: `s \\ t = s ∩ tᶜ`. Now let us **prove** this identity.

At the element level, both sides say the same thing:
- `x ∈ s \\ t` means `x ∈ s ∧ x ∉ t`
- `x ∈ s ∩ tᶜ` means `x ∈ s ∧ x ∈ tᶜ`, which is `x ∈ s ∧ x ∉ t`

So the proof is: `ext x`, then `constructor`, then show each direction
by extracting and reassembling the components.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔`
3. **Forward**: `intro hx`, `obtain ⟨hs, ht⟩ := hx`, `exact ⟨hs, ht⟩`
4. **Backward**: same structure in reverse
"

/-- Set difference equals intersection with complement. -/
Statement (α : Type) (s t : Set α) : s \ t = s ∩ tᶜ := by
  Hint "Use `ext x` to reduce the set equality to a membership
  biconditional, then `constructor` to split the `↔`."
  ext x
  constructor
  -- Forward: s \ t → s ∩ tᶜ
  · Hint "Given `x ∈ s \\ t`, prove `x ∈ s ∩ tᶜ`. Both sides have the
    same components (`x ∈ s` and `x ∉ t`), just packaged differently.
    Start with `intro hx` then destructure."
    Hint (hidden := true) "`intro hx` then `obtain ⟨hs, ht⟩ := hx` then
    `exact ⟨hs, ht⟩`."
    intro hx
    Hint "Destructure `hx` with `obtain ⟨hs, ht⟩ := hx`."
    obtain ⟨hs, ht⟩ := hx
    Hint "Now `hs : x ∈ s` and `ht : x ∉ t`. The goal is `x ∈ s ∩ tᶜ`,
    which is `x ∈ s ∧ x ∈ tᶜ`. Since `x ∈ tᶜ` IS `x ∉ t`, the pieces
    match. Use `exact ⟨hs, ht⟩`."
    exact ⟨hs, ht⟩
  -- Backward: s ∩ tᶜ → s \ t
  · Hint "Given `x ∈ s ∩ tᶜ`, prove `x ∈ s \\ t`. Same idea:
    destructure and reassemble."
    Hint (hidden := true) "`intro hx` then `obtain ⟨hs, ht⟩ := hx` then
    `exact ⟨hs, ht⟩`."
    intro hx
    Hint "Destructure `hx` with `obtain ⟨hs, ht⟩ := hx`."
    obtain ⟨hs, ht⟩ := hx
    Hint "`hs : x ∈ s` and `ht : x ∈ tᶜ` (= `x ∉ t`). The goal is
    `x ∈ s \\ t`, which is `x ∈ s ∧ x ∉ t`. Use `exact ⟨hs, ht⟩`."
    exact ⟨hs, ht⟩

Conclusion "
You proved that set difference is not a new primitive — it is
**intersection with complement**: `s \\ t = s ∩ tᶜ`.

This is a common pattern in mathematics: seemingly distinct operations
turn out to be combinations of more fundamental ones. Here, the four
set operations (∪, ∩, ᶜ, \\) reduce to just three (∪, ∩, ᶜ), since
difference is derivable.

The proof was straightforward because both sides have *exactly the
same logical content* — `x ∈ s ∧ x ∉ t`. The `ext` + `constructor`
pattern made this visible.

**New idiom: `exact ⟨a, b⟩`**. You already know that
`obtain ⟨a, b⟩ := h` *destructs* a pair (splits `h : P ∧ Q` into
its components). In this proof you saw the dual: `exact ⟨hs, ht⟩`
*constructs* a pair — it builds a conjunction from two pieces already
in context. Think of `⟨...⟩` as anonymous pair notation: `obtain`
takes it apart, `exact` puts it together.
"

/-- `Set.diff_eq` states `s \\ t = s ∩ tᶜ`. -/
TheoremDoc Set.diff_eq as "Set.diff_eq" in "Set"

NewTheorem Set.diff_eq

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.diff_eq sdiff_eq
