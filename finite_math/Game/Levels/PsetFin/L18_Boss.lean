import Game.Metadata

World "PsetFin"
Level 18

Title "Boss: Phase 1 Complete"

Introduction "
# Boss: Integrating All Fin Skills

This boss has two parts that draw on all three lecture worlds.

**Part 1 — Comparing two tuples**: `f` is described by its head
and tail, `g` by a pointwise formula. Prove they're equal.

Strategy: first **reconstruct** `f` from head + tail (FinTuples
Level 19 recipe), then use **ext + case split** to compare
with `g` index by index.

**Part 2 — Non-constant tuple**: Prove that `f` has at least two
different values.

Strategy: provide a witness index where `f` differs from `f 0`.

Moves required:
- Front reconstruction (`.symm` + `rw ... at`)
- Function extensionality (`ext`)
- Case analysis with impossible-branch elimination (`absurd`)
- Universally quantified rewrite (`rw [hg]`)
- Existential witness (`use`)
- Inequality pattern
"

/-- Comparing reconstructed tuples and finding non-constant entries. -/
Statement (f g : Fin 3 → ℕ)
    (hf0 : f 0 = 2) (hft : Fin.tail f = ![4, 6])
    (hg : ∀ i : Fin 3, g i = 2 * i.val + 2) :
    f = g ∧ ∃ i : Fin 3, f i ≠ f 0 := by
  -- Step 1: Reconstruct f
  Hint "First, determine what `f` actually is.
  Use the front reconstruction pattern:
  `have hf : f = ![2, 4, 6] := by`
  then inside, start with `have key := (Fin.cons_self_tail f).symm`."
  have hf : f = ![2, 4, 6] := by
    Hint (hidden := true) "`have key := (Fin.cons_self_tail f).symm`
    gives `key : f = Fin.cons (f 0) (Fin.tail f)`.
    Then `rw [hf0, hft] at key` substitutes the known parts.
    Finally `exact key`."
    have key := (Fin.cons_self_tail f).symm
    rw [hf0, hft] at key
    exact key
  Hint "Good! Now `hf : f = ![2, 4, 6]`.
  Split the conjunction with `constructor`."
  constructor
  -- Part 1: f = g
  · Hint "Show the functions agree at every index.
    Use `ext ⟨v, hv⟩`, then `rw [hf, hg]` to substitute both."
    ext ⟨v, hv⟩
    Hint (hidden := true) "After `rw [hf, hg]`, the goal at each
    index reduces to a numerical equality. Case-split on `v`
    and use `rfl` for each valid case."
    rw [hf, hg]
    cases v with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => rfl
        | succ k => exact absurd hv (by omega)
  -- Part 2: f has non-constant values
  · Hint "Find an index where `f` differs from `f 0`.
    Since `f = ![2, 4, 6]`, any index besides 0 works."
    Hint (hidden := true) "`use ⟨1, by omega⟩` provides the witness.
    Then `rw [hf]` substitutes the known tuple, and the
    inequality between `4` and `2` closes automatically."
    use ⟨1, by omega⟩
    rw [hf]
    intro h; cases h

Conclusion "
Congratulations — you've completed **Phase 1: Finite Types**!

Here's everything in your toolkit:

**Construction**: `⟨k, by omega⟩`, `use`, `![a, b, c]`, `Fin.cons`, `vecSnoc`

**Extraction**: `.val`, `.isLt`, `Fin.val_last`, `Fin.val_succ`, `Fin.val_castSucc`

**Equality**: `ext` (for Fin or functions), `Fin.ext_iff`, `rfl`

**Inequality**: `intro h; cases h` (literals), `rw [Fin.ext_iff] at h; omega` (general)

**Case analysis**: `cases x with | mk v hv` + nested `cases v`

**Reconstruction**: `Fin.cons_self_tail.symm` (front), `vecSnoc_self_init.symm` (back)

**Impossible cases**: `exact absurd hv (by omega)`

**Why do we need more than `Fin n -> alpha`?** Tuples are powerful
— but they're *ordered* and *indexed*. Not everything in mathematics
has a natural ordering or an index. The set of prime divisors of 30
is `(2, 3, 5)` — but why should 2 come first? The set of elements
in a group with order dividing 6 has no canonical indexing. These
are collections defined by a **membership predicate** (`x in S` if
`P x`), not by position.

Phase 2 introduces `Finset` — unordered finite collections with
decidable membership — to handle exactly this. You'll build finite
sets, prove membership facts, and compute with set operations. The
`Fin` skills you've mastered will appear throughout: `Finset`
membership proofs often reduce to `Fin`-level reasoning.

The most direct bridge: `Finset.range n = {0, 1, ..., n-1}` is
essentially `Fin n` repackaged as an unordered set. Where `Fin n`
gives you *indexed access* (`f i` for `i : Fin n`), `Finset.range n`
gives you *membership* (`k in Finset.range n iff k < n`). Same
elements, different interface — and you'll see how the `Fin`-level
reasoning you've mastered transfers directly to the `Finset` world.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
