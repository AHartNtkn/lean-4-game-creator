import Game.Metadata

World "Finale"
Level 16

Title "Bijective from Injective"

Introduction "
# The Course Capstone: Constructing Bijectivity

In Level 13, you proved surjective endofunctions are injective.
In the boss (Level 14), you proved injective endofunctions are
surjective — and along the way, you showed that the image of an
injective endofunction equals the entire universe.

Now put it all together. Given that `f` is injective and that
its image covers `Finset.univ`, construct a proof that `f` is
**bijective**: both injective AND surjective.

`Function.Bijective f` is defined as
`Function.Injective f ∧ Function.Surjective f`.

**The proof plan**:
1. Split the conjunction with `constructor`
2. The injective half is immediate from `hf`
3. For the surjective half: since `image f univ = univ`, every
   element `y` is in the image — extract its preimage
"

/-- An injective endofunction with full image is bijective. -/
Statement (n : ℕ) (f : Fin n → Fin n) (hf : Function.Injective f)
    (heq : Finset.univ.image f = Finset.univ) :
    Function.Bijective f := by
  Hint "`Function.Bijective f` is `Injective f ∧ Surjective f`.
  Split the conjunction."
  Hint (hidden := true) "Try `constructor`."
  constructor
  · Hint "The injective half is immediate from `hf`."
    Hint (hidden := true) "Try `exact hf`."
    exact hf
  · Hint "For surjectivity: introduce the target element `y`."
    Hint (hidden := true) "Try `intro y`."
    intro y
    Hint "Since `image f univ = univ` and `y` is in `univ`,
    `y` must be in `image f univ`. Establish this membership."
    Hint (hidden := true) "Try:
    `have hymem : y in Finset.univ.image f := by rw [heq]; exact Finset.mem_univ y`"
    have hymem : y ∈ Finset.univ.image f := by
      rw [heq]
      exact Finset.mem_univ y
    Hint "Rewrite using `Finset.mem_image` to expose the existential:
    there exists `x` in `univ` with `f x = y`. Extract the witness."
    Hint (hidden := true) "Try:
    `rw [Finset.mem_image] at hymem`
    `obtain ⟨x, _, hfx⟩ := hymem`
    `exact ⟨x, hfx⟩`"
    rw [Finset.mem_image] at hymem
    obtain ⟨x, _, hfx⟩ := hymem
    exact ⟨x, hfx⟩

Conclusion "
# Congratulations!

You have completed **Finite Mathematics**.

You just proved that an injective endofunction on `Fin n` is
**bijective** — injective AND surjective. `Function.Bijective`
packages both properties into a single conjunction, which is the
form you would use in further proofs (e.g., constructing inverse
functions, proving equalities of types via `Equiv.ofBijective`).

**The proof combined**:
- `constructor` to split `Bijective` into its two halves
- `hf` for injectivity (given)
- The witness extraction pattern (`mem_image` + `obtain`) from
  the boss, applied to `heq` for surjectivity

**The full equivalence**: For any $f : \\text{Fin}\\,n \\to
\\text{Fin}\\,n$:
$$\\text{injective} \\iff \\text{surjective} \\iff \\text{bijective}$$

Knowing any one of these properties gives you all three.

**The course in retrospect**: You built this result from the
ground up:
- **Phase 1**: Learned to navigate `Fin n` and build tuples
- **Phase 2**: Mastered `Finset` membership, operations, and images
- **Phase 3**: Developed cardinality reasoning and the
  cardinality sandwich
- **Phase 4**: Wielded big operators and summation formulas
- **Phase 5**: Explored binomial coefficients and powerset
  decompositions
- **Phase 6**: Extended to products, finitely supported
  functions, and matrices
- **Phase 7**: Applied counting techniques — bijection,
  injection, pigeonhole, double counting

**What comes next**: The tools you've learned are the foundation
for:

- **Group theory**: Lagrange's theorem is a fiber-decomposition
  argument applied to cosets
- **Graph theory**: Counting edges, paths, and colorings in
  finite graphs uses exactly these tools
- **Ramsey theory**: The pigeonhole principle generalizes to
  Ramsey numbers, where any 2-coloring of a large enough
  complete graph contains a monochromatic clique
- **Generating functions**: Big operators over formal power series
  extend the summation techniques to infinite settings
- **Linear algebra**: Matrices over finite fields connect the
  matrix world to modular arithmetic and coding theory

These are all active areas of formalization in Mathlib. The
proof patterns you've practiced — induction, decomposition,
bounding, and contradiction — transfer directly.
"

/-- `Function.Bijective f` means `f` is both injective and surjective:
`Function.Injective f ∧ Function.Surjective f`.

A bijective function is a one-to-one correspondence: every output
has exactly one preimage.
-/
DefinitionDoc Function.Bijective as "Function.Bijective"

NewDefinition Function.Bijective

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent shortcuts
DisabledTheorem Finite.surjective_of_injective Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective
