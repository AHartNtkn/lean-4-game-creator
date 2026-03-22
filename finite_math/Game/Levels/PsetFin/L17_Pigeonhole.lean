import Game.Metadata

World "PsetFin"
Level 17

Title "The Pigeonhole Principle (Concrete)"

Introduction "
# Three Pigeons, Two Holes

The **pigeonhole principle** says: if you put more objects into
fewer boxes, at least two objects share a box.

Formally: any function `f : Fin 3 -> Fin 2` must send two
different inputs to the same output. There are 3 inputs but
only 2 possible outputs, so a collision is inevitable.

This is your first real **theorem from combinatorics** — and
you can prove it using only the tools from Phase 1.

**Strategy**:
1. Classify each `Fin 2` value: every `x : Fin 2` is either `0` or `1`
2. Apply the classification to `f 0` and `f 1`
3. If they're equal: witnesses are `0` and `1`
4. If they differ: check `f 2` — it must match one of them
"

/-- Any function from Fin 3 to Fin 2 has a collision. -/
Statement (f : Fin 3 → Fin 2) : ∃ i j : Fin 3, i ≠ j ∧ f i = f j := by
  Hint "**Fair warning**: this proof is intentionally tedious. You'll
  brute-force the pigeonhole principle for 3 → 2 by exhaustive case
  analysis — roughly 50 tactic steps across 6 branches. The point is
  to feel the pain: case analysis doesn't scale. In the Cardinality
  world, you'll prove the same result for ANY n in just 4 lines using
  counting tools. The contrast between brute force and elegance is the
  lesson."
  Hint "**Full strategy overview** — the proof has three phases:

  1. **Classify**: Prove a helper `classify : forall x : Fin 2, x = 0 or x = 1`
  2. **Apply**: Use `classify` on `f 0`, `f 1`, and (when needed) `f 2`
  3. **Case tree**: 6 branches, each ending with `use i, j; constructor; intro h; cases h; rw [...]`

  If `f 0` and `f 1` have the same value: collision at `0, 1`.
  If they differ: check `f 2` — it must match one of them."
  -- Helper: every Fin 2 element is 0 or 1
  Hint "First, prove a helper: every element of `Fin 2` is `0` or `1`.
  Use `have classify : forall x : Fin 2, x = 0 or x = 1 := by ...`"
  Hint (hidden := true) "Inside the `have`, destructure:
  `intro (v, hv); cases v with | zero => left; rfl | succ n => ...`
  For `succ n`: `cases n with | zero => right; rfl | succ m => exact absurd hv (by omega)`"
  have classify : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro ⟨v, hv⟩
    cases v with
    | zero => left; rfl
    | succ n =>
      cases n with
      | zero => right; rfl
      | succ m => exact absurd hv (by omega)
  Hint "Now classify `f 0` and `f 1`:
  `have h0 := classify (f 0)` and `have h1 := classify (f 1)`."
  have h0 := classify (f 0)
  have h1 := classify (f 1)
  Hint "**Strategy map** — the case tree has 6 branches:

  - `f 0 = 0, f 1 = 0`: collision at 0 and 1 (done)
  - `f 0 = 0, f 1 = 1`: check `f 2` — matches 0 or 1
  - `f 0 = 1, f 1 = 1`: collision at 0 and 1 (done)
  - `f 0 = 1, f 1 = 0`: check `f 2` — matches 0 or 1

  Every branch ends the same way: `use i, j; constructor; intro h; cases h; rw [...]`.

  Start: `cases h0 with | inl h0 => ... | inr h0 => ...`"
  Hint (hidden := true) "Inside each `h0` branch:
  `cases h1 with | inl h1 => ... | inr h1 => ...`

  In matching-value branches (both 0 or both 1):
  `use 0, 1; constructor; intro h; cases h; rw [h0, h1]`

  In differing-value branches:
  `have h2 := classify (f 2)` then case-split on `h2`.
  Each sub-branch: `use i, 2; constructor; intro h; cases h; rw [hi, h2]`
  where `i` is 0 or 1 depending on which value `f 2` matches."
  cases h0 with
  | inl h0 =>
    cases h1 with
    | inl h1 =>
      -- f 0 = 0, f 1 = 0: collision at 0 and 1
      Hint "Both `f 0` and `f 1` map to `0` — collision at indices 0 and 1.
      Provide the witnesses and prove the conjunction."
      Hint (hidden := true) "`use 0, 1; constructor; · intro h; cases h; · rw [h0, h1]`"
      use 0, 1
      constructor
      · intro h; cases h
      · rw [h0, h1]
    | inr h1 =>
      -- f 0 = 0, f 1 = 1: check f 2
      Hint "The outputs differ (`f 0 = 0`, `f 1 = 1`), so no collision
      yet. Check `f 2` — it must equal `0` or `1`, matching one of them."
      Hint (hidden := true) "`have h2 := classify (f 2)` then case-split on `h2`."
      have h2 := classify (f 2)
      cases h2 with
      | inl h2 =>
        Hint (hidden := true) "`f 2 = 0 = f 0`: use `0, 2; constructor; · intro h; cases h; · rw [h0, h2]`"
        use 0, 2
        constructor
        · intro h; cases h
        · rw [h0, h2]
      | inr h2 =>
        Hint (hidden := true) "`f 2 = 1 = f 1`: use `1, 2; constructor; · intro h; cases h; · rw [h1, h2]`"
        use 1, 2
        constructor
        · intro h; cases h
        · rw [h1, h2]
  | inr h0 =>
    cases h1 with
    | inr h1 =>
      -- f 0 = 1, f 1 = 1: collision at 0 and 1
      Hint "Both `f 0` and `f 1` map to `1` — collision at indices 0 and 1."
      Hint (hidden := true) "`use 0, 1; constructor; · intro h; cases h; · rw [h0, h1]`"
      use 0, 1
      constructor
      · intro h; cases h
      · rw [h0, h1]
    | inl h1 =>
      -- f 0 = 1, f 1 = 0: check f 2
      Hint "The outputs differ (`f 0 = 1`, `f 1 = 0`), so no collision
      yet. Check `f 2` — it must match one of them."
      Hint (hidden := true) "`have h2 := classify (f 2)` then case-split on `h2`."
      have h2 := classify (f 2)
      cases h2 with
      | inl h2 =>
        Hint (hidden := true) "`f 2 = 0 = f 1`: use `1, 2; constructor; · intro h; cases h; · rw [h1, h2]`"
        use 1, 2
        constructor
        · intro h; cases h
        · rw [h1, h2]
      | inr h2 =>
        Hint (hidden := true) "`f 2 = 1 = f 0`: use `0, 2; constructor; · intro h; cases h; · rw [h0, h2]`"
        use 0, 2
        constructor
        · intro h; cases h
        · rw [h0, h2]

Conclusion "
You've proved the **pigeonhole principle** for `Fin 3 -> Fin 2`:
any function from a 3-element set to a 2-element set must have
a collision.

The proof strategy was:
1. **Classify** each output as `0` or `1`
2. **Compare** outputs at pairs of inputs
3. **Find** two inputs with the same output

Every tool in this proof came from Phase 1:
- Case analysis on `Fin 2` (MeetFin)
- Existential witnesses with `use` (MeetFin)
- Inequality pattern `intro h; cases h` (MeetFin)
- Rewriting with hypotheses (FinTuples)

**The abstract pigeonhole principle**: This generalizes. For any
function `f : Fin (n+1) -> Fin n`, there must exist `i j` with
`i /= j` and `f i = f j`. More inputs than outputs forces a
collision — always. The concrete proof here used exhaustive case
analysis, which doesn't scale: for `Fin 100 -> Fin 99`, you'd
need astronomical case splits. In the Finset worlds ahead, you'll
learn cardinality tools that prove pigeonhole for any `n` in a
few lines.

**The cardinality consequence**: If there were a collision-free
function from `Fin 3` to `Fin 2`, we could embed a 3-element set
into a 2-element set — which is impossible. So `|Fin 3| > |Fin 2|`,
confirming that `Fin 3` is genuinely 'larger than' `Fin 2`. More
importantly, the parameter `n` in `Fin n` is *recoverable* from
the type: `Fin n` and `Fin m` can only be equivalent (have a
bijection between them) when `n = m`. This is what makes `Fin n`
the canonical finite type — it uniquely represents 'a type with
exactly n elements.'
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
