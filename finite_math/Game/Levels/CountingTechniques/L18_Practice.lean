import Game.Metadata

World "CountingTechniques"
Level 18

Title "Practice: The Mutual Injection Principle"

Introduction "
# Practice: Injections Both Ways

Before the boss, practice combining counting techniques.

**The problem**: Given injective functions `f : Fin m -> Fin n`
and `g : Fin n -> Fin m`, prove `m = n`.

Intuitively: `f` injective means `m <= n` (the source fits in the
target). `g` injective means `n <= m`. Together: `m = n`.

**Proof strategy**:
1. Apply `Fintype.card_le_of_injective` to `f` — get `m <= n`
2. Apply `Fintype.card_le_of_injective` to `g` — get `n <= m`
3. Evaluate with `card_fin`
4. Combine with `omega` (which sees `m <= n` and `n <= m` imply `m = n`)

This is the **Mutual Injection Principle**: if two finite types
can each be injected into the other, they have equal cardinality.
It's a consequence of the sandwich argument (`le_antisymm`) from
Level 4.
"

/-- Injections in both directions imply equal cardinality. -/
Statement (m n : ℕ) (f : Fin m → Fin n) (g : Fin n → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    m = n := by
  Hint "Apply the injection bound to `f` to get `card (Fin m) <= card (Fin n)`."
  Hint (hidden := true) "Try:
  `have h1 := Fintype.card_le_of_injective f hf`"
  have h1 := Fintype.card_le_of_injective f hf
  Hint "Evaluate the cardinalities to get `m <= n`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin] at h1`."
  rw [Fintype.card_fin, Fintype.card_fin] at h1
  Hint "Now do the same for `g` — apply the injection bound
  to get `card (Fin n) <= card (Fin m)`."
  Hint (hidden := true) "Try:
  `have h2 := Fintype.card_le_of_injective g hg`"
  have h2 := Fintype.card_le_of_injective g hg
  Hint "Evaluate to get `n <= m`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin] at h2`."
  rw [Fintype.card_fin, Fintype.card_fin] at h2
  Hint "Now `h1 : m <= n` and `h2 : n <= m`. Together these give `m = n`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The Mutual Injection Principle:
1. `card_le_of_injective f hf` — injection `f` gives `m <= n`
2. `card_le_of_injective g hg` — injection `g` gives `n <= m`
3. `rw [card_fin]` — evaluate concrete cardinalities
4. `omega` — sandwich: `m <= n` and `n <= m` force `m = n`

This is `le_antisymm` (Level 4) applied to concrete types.
The two opposing injection bounds combine into equality.

**In plain mathematics**: The Cantor-Bernstein theorem (also called
the Schroder-Bernstein theorem) states that if there exist injections
`A -> B` and `B -> A`, then `|A| = |B|`. For finite sets, the proof
is elementary — just the sandwich argument you used above.

For infinite sets, the proof is much harder. The injection
`f : A -> B` no longer gives a *numerical* inequality (there is
no finite cardinality to compare). Instead, one must construct an
explicit bijection by partitioning both sets into alternating
chains of `f` and `g`-images, then defining the bijection piecewise.
The finite case avoids all this because `|A| <= |B|` is a statement
about natural numbers, and `le_antisymm` on natural numbers is trivial.

You're ready for the boss.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Force the injection-bound approach, don't let surjection shortcut
DisabledTheorem Fintype.card_le_of_surjective Fintype.card_of_bijective
