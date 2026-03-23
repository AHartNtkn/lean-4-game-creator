import Game.Metadata

World "Finale"
Level 7

Title "Pigeonhole in the Wild"

Introduction "
# Applying Pigeonhole to Modular Arithmetic

Every level so far has worked with abstract functions between
Fin types. But the pigeonhole principle is most powerful when
applied to **concrete mathematical situations**.

**Claim**: Given any $n + 1$ natural numbers, two of them share
the same remainder when divided by $n$.

The 'bins' are the $n$ possible remainders ($0, 1, \\ldots, n-1$),
and the 'pigeons' are the $n + 1$ numbers. Since there are more
numbers than bins, two must land in the same bin.

**The proof plan**:
1. Assume for contradiction that no two values share a remainder
2. Define the remainder function $g(i) = a(i) \\bmod n$, which
   maps into $\\text{Fin}\\,n$
3. From the assumption, $g$ is injective
4. Derive a contradiction via image cardinality (same as Level 6)
"

/-- Among any n+1 natural numbers, two share the same remainder mod n. -/
Statement (n : ℕ) (hn : n ≥ 1) (a : Fin (n + 1) → ℕ) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ a i % n = a j % n := by
  -- Step 1: Contradiction setup
  Hint "Assume for contradiction that no two values share a remainder."
  Hint (hidden := true) "Try `by_contra hall` then `push_neg at hall`."
  by_contra hall
  push_neg at hall
  -- hall : ∀ i j, i ≠ j → a i % n ≠ a j % n
  -- Step 2: Define remainder function g : Fin (n+1) → Fin n
  Hint "First prove that every remainder is strictly less than `n`.
  This gives the bound needed to construct elements of `Fin n`."
  Hint (hidden := true) "Try:
  `have hlt : forall i, a i % n < n := fun i => Nat.mod_lt (a i) (by omega)`"
  have hlt : ∀ i, a i % n < n := fun i => Nat.mod_lt (a i) (by omega)
  Hint "Now define the remainder function using `let`. Each input maps
  to its remainder mod `n`, packaged as an element of `Fin n`."
  Hint (hidden := true) "Try:
  `let g : Fin (n + 1) -> Fin n := fun i => ⟨a i % n, hlt i⟩`"
  let g : Fin (n + 1) → Fin n := fun i => ⟨a i % n, hlt i⟩
  -- Step 3: g is injective (from the assumption)
  Hint "From the assumption that no two values share a remainder,
  prove that `g` is injective."
  Hint (hidden := true) "Try:
  `have hinj : Function.Injective g := by`
  `  intro x y hxy`
  `  by_contra hne`
  `  exact hall x y hne (Fin.ext_iff.mp hxy)`"
  have hinj : Function.Injective g := by
    Hint "To prove injectivity, assume `g x = g y` and show `x = y`."
    Hint (hidden := true) "Try `intro x y hxy`."
    intro x y hxy
    Hint "You have `hxy : g x = g y`. Since `g` wraps values in `Fin n`,
    this means the underlying remainders are equal. Use contradiction:
    assume `x ≠ y` and derive `False` from `hall`."
    Hint (hidden := true) "Try `by_contra hne`."
    by_contra hne
    Hint "You have `hne : x ≠ y` and `hxy : g x = g y`. Apply
    `hall x y hne` — it says distinct indices have distinct remainders.
    Extract the remainder equality from `hxy` using `Fin.ext_iff.mp`."
    Hint (hidden := true) "Try `exact hall x y hne (Fin.ext_iff.mp hxy)`."
    exact hall x y hne (Fin.ext_iff.mp hxy)
  -- Step 4: Contradiction from image cardinality
  Hint "Now derive a contradiction: the image of `g` on `Finset.univ`
  has cardinality $n + 1$ (by injectivity) but sits inside a set
  of size $n$."
  Hint (hidden := true) "Try:
  `have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin (n + 1))) hinj`
  `rw [Finset.card_univ, Fintype.card_fin] at himg`"
  have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin (n + 1))) hinj
  rw [Finset.card_univ, Fintype.card_fin] at himg
  Hint (hidden := true) "Try:
  `have hsub := Finset.card_le_card (Finset.subset_univ (Finset.univ.image g))`
  `rw [Finset.card_univ, Fintype.card_fin] at hsub`
  `omega`"
  have hsub := Finset.card_le_card (Finset.subset_univ (Finset.univ.image g))
  rw [Finset.card_univ, Fintype.card_fin] at hsub
  omega

Conclusion "
**Pigeonhole applied to modular arithmetic**: among any $n + 1$
natural numbers, two share the same remainder mod $n$.

The proof pattern:
1. Assume no two values collide (by contradiction)
2. Define the 'binning' function ($a(i) \\bmod n$)
3. Derive injectivity from the no-collision assumption
4. Contradict via image cardinality ($n + 1 \\le n$)

**The key skill** this level exercises is **modeling**: turning
a concrete mathematical claim into the abstract pigeonhole
framework. You had to:
- Identify what the 'pigeons' are (the $n + 1$ values)
- Identify what the 'holes' are (the $n$ remainders)
- Define the function that assigns pigeons to holes
- Apply the abstract machinery from Levels 5-6

This modeling step — going from a real problem to the abstract
template — is the essence of applying combinatorics in practice.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent library pigeonhole shortcuts
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
