import Game.Metadata

World "PreimageWorld"
Level 15

Title "Composing Library Results"

TheoremTab "Set"

Introduction "
# A New Proof Strategy: Rewriting with Library Theorems

In Levels 6-12, you proved set equalities by `ext x; constructor` —
reducing to element-wise membership and proving both directions.
There is another approach: **compose library results via `rw`**.

Instead of starting from scratch, you can chain the identities you
already proved as rewrite rules. Each `rw` step transforms the
expression using a known theorem, and after enough rewrites the
two sides match automatically.

**Your task**: Prove `f ⁻¹' (s ∩ tᶜ) = f ⁻¹' s ∩ (f ⁻¹' t)ᶜ`.

You already know:
- `Set.preimage_inter`: `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t`
- `Set.preimage_compl`: `f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ`

Apply them in sequence:
1. `rw [Set.preimage_inter]` — distribute over `∩`
2. `rw [Set.preimage_compl]` — distribute over `ᶜ`

Two rewrites, no `ext`, no `constructor`. The library does the work.

This technique scales: the boss level will use the same approach
with four rewrites to prove that preimage preserves set difference.
"

/-- Preimage distributes over intersection with complement. -/
Statement (α β : Type) (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ tᶜ) = f ⁻¹' s ∩ (f ⁻¹' t)ᶜ := by
  Hint "Use `rw [Set.preimage_inter]` to distribute preimage over
  the intersection. This uses the theorem you proved in Level 8."
  Hint (hidden := true) "The full proof is:
  `rw [Set.preimage_inter]`
  `rw [Set.preimage_compl]`"
  rw [Set.preimage_inter]
  Hint "Good! Now the left side has `f ⁻¹' tᶜ`. Use
  `rw [Set.preimage_compl]` to distribute preimage over the
  complement. This uses the theorem from Level 10."
  Hint (hidden := true) "`rw [Set.preimage_compl]`"
  rw [Set.preimage_compl]

Conclusion "
Two rewrites — done! Compare this with the `ext x; constructor`
approach, which would have required introducing `x`, splitting the
biconditional, destructuring conjunctions, and handling negation
in both directions.

**When to use each approach**:

| Strategy | When to use |
|---|---|
| `ext x; constructor; ...` | Proving a NEW identity from scratch |
| `rw [theorem1]; rw [theorem2]; ...` | Composing KNOWN identities |

The rewrite approach is more concise and reads more like a
mathematical proof: \"by preimage-inter and preimage-compl.\"
It is also closer to how mathematicians actually reason — citing
known results rather than reproving everything from definitions.

The boss level will ask you to prove preimage preserves set
difference using this same strategy with four rewrites. You now
have the technique; the boss tests whether you can identify which
theorems to compose.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl ext funext
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
