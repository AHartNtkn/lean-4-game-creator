import Game.Metadata

World "AbstractionLadder"
Level 8

Title "Permutations Preserve Length"

Introduction "
# Using Perm.length_eq

You learned that `List.Perm.length_eq` gives:

`hp.length_eq : l₁.length = l₂.length`
  (from `hp : l₁.Perm l₂`)

But you haven't used it in a proof yet. Time to practice.

**Your task**: Given a permutation `hp : l₁.Perm l₂` and a known
length `hlen : l₁.length = 5`, prove `l₂.length = 5`.

**Strategy**: Use `hp.length_eq` to connect the two lengths, then
rewrite with the backward direction (`←`) to replace `l₂.length`
with `l₁.length`.
"

/-- Permutations preserve length: if l₁ has 5 elements and l₁ ~ l₂, then l₂ has 5 elements. -/
Statement (l₁ l₂ : List ℕ) (hp : l₁.Perm l₂) (hlen : l₁.length = 5) :
    l₂.length = 5 := by
  Hint "Use `rw [← hp.length_eq]` to replace `l₂.length` with
  `l₁.length` in the goal. The `←` means 'use the equation
  right-to-left.'"
  Hint (hidden := true) "Try:
  `rw [← hp.length_eq]`
  `exact hlen`"
  rw [← hp.length_eq]
  exact hlen

Conclusion "
You used `← hp.length_eq` to rewrite the goal: since
`hp.length_eq : l₁.length = l₂.length`, the backward rewrite
replaces `l₂.length` with `l₁.length`.

**Tip**: The `.symm` method flips an equality. So `hp.length_eq.symm`
gives `l₂.length = l₁.length`. In the boss level, you'll use
`exact hp.length_eq.symm` to close a goal of the form
`l₂.length = l₁.length` directly.

Both `← rw` and `.symm` handle direction mismatches — use whichever
fits the context.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
