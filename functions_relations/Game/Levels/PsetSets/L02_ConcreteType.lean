import Game.Metadata

World "PsetSets"
Level 2

Title "Concrete Type Exercise"

TheoremTab "Set"

Introduction "
# Problem Set: Level 2

All the levels in the lecture worlds used either `Nat` for concrete
examples or abstract sets `(alpha : Type) (s t : Set alpha)`. This
level uses a **different concrete type**: the integers `Z`.

Prove that 3 and -5 are odd:

$$\\{x : \\mathbb{Z} \\mid x = 3 \\lor x = -5\\} \\subseteq \\{x \\mid \\exists\\, k : \\mathbb{Z},\\; x = 2k + 1\\}$$

The new aspect is working over `Z` — negative numbers exist, and you
need to find the correct witness `k` for each case.
"

/-- 3 and -5 are odd integers. -/
Statement : {x : ℤ | x = 3 ∨ x = -5} ⊆ {x | ∃ k : ℤ, x = 2 * k + 1} := by
  Hint "Start with `intro x hx` for the subset proof. Then case-split
  on the disjunction in `hx`."
  intro x hx
  Hint (hidden := true) "Key move: `cases hx with | inl h | inr h` splits
  the two cases. In each case, use `show` to expose the existential goal,
  `rw [h]`, then `use` the appropriate witness, then `omega`."
  cases hx with
  | inl h =>
    Hint "`h : x = 3`. Use `show` to expose the goal as an existential,
    rewrite with `h`, then provide a witness."
    Hint (hidden := true) "`show exists k : Z, x = 2 * k + 1` then
    `rw [h]` then `use 1` then `omega`."
    show ∃ k : ℤ, x = 2 * k + 1
    rw [h]
    use 1
    omega
  | inr h =>
    Hint "`h : x = -5`. Same approach — find a `k` so that `-5 = 2k + 1`,
    i.e., `k = -3`."
    Hint (hidden := true) "`show exists k : Z, x = 2 * k + 1` then
    `rw [h]` then `use (-3)` then `omega`."
    show ∃ k : ℤ, x = 2 * k + 1
    rw [h]
    use (-3)
    omega

Conclusion "
You proved a concrete-type subset on `Z`. The proof combined:
- `intro` + `cases` for subset and disjunction (from Set/Subset World)
- `show` to expose the set membership as a predicate (from Set World)
- `rw` to substitute the concrete value (universal)
- `use` to provide an existential witness (from Indexed Ops World)
- `omega` for integer arithmetic (NNG4 baseline)

**Key observation**: The membership-to-predicate reduction works
identically regardless of the type. Whether the type is `Nat`, `Z`, or
an abstract type `alpha`, `x in S` becomes a predicate on `x`. The
proof *structure* is the same — only the arithmetic changes.

**Working with Z**: Finding `k = -3` for `-5 = 2k + 1` required
reasoning about negative numbers — something that does not arise with
`Nat`. This is why concrete-type exercises matter: they reveal whether
you have internalized the proof pattern or just memorized a particular
surface form.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
