import Game.Metadata

World "HomPset"
Level 7

Title "Boss — Surjective iff Full Range"

Introduction
"
The boss of Kernel and Image was `ker(f) = ⊥ ↔ f injective`.
Now prove the dual: `range(f) = ⊤ ↔ f surjective`.

**Forward** (`range = ⊤ → surjective`): Given any `y : H`, show
`∃ x, f x = y`. Since `range = ⊤`, the element `y` is in `f.range`
(because it's in `⊤`), and range membership gives the witness.

**Backward** (`surjective → range = ⊤`): Prove two subgroups are equal
using `ext`. For any `y`: `y ∈ f.range` iff `y ∈ ⊤`. The right-to-left
direction uses surjectivity (Level 6). The left-to-right is trivial
(everything is in `⊤`).

Start with `refine ⟨?_, ?_⟩` to split the `↔`.
"

/-- Disabled — you are proving this yourself right now. -/
TheoremDoc MonoidHom.range_eq_top as "MonoidHom.range_eq_top" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.range_eq_top MonoidHom.range_eq_top_of_surjective

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f.range = ⊤ ↔ Function.Surjective f := by
  Hint "Split the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · -- Forward: range = ⊤ → surjective
    Hint "Introduce the hypothesis and unfold surjectivity:
    `intro hr y`.

    The goal becomes `∃ x, f x = y`."
    intro hr y
    Hint "You need `y ∈ f.range` to extract a witness. Since
    `{hr} : f.range = ⊤` and `y ∈ ⊤` is always true, you can
    get `y ∈ f.range`.

    Create this with `have`:
    `have hy : y ∈ f.range := by rw [{hr}]; exact Subgroup.mem_top y`."
    Branch
      -- Alternative: start from mem_top and rewrite backward
      Hint "You started from `Subgroup.mem_top y`. Now replace `⊤`
      with `f.range` using `rw [← {hr}] at hy`, then unfold range
      membership with `rw [MonoidHom.mem_range] at hy`."
      have hy : y ∈ (⊤ : Subgroup H) := Subgroup.mem_top y
      rw [← hr] at hy
      rw [MonoidHom.mem_range] at hy
      exact hy
    have hy : y ∈ f.range := by rw [hr]; exact Subgroup.mem_top y
    Hint "Now `{hy} : y ∈ f.range`. Unfold this to get the existential:
    `rw [MonoidHom.mem_range] at {hy}`."
    rw [MonoidHom.mem_range] at hy
    Hint (hidden := true) "`exact {hy}`"
    exact hy
  · -- Backward: surjective → range = ⊤
    Hint "Introduce the surjectivity hypothesis: `intro hs`.

    To prove two subgroups are equal, use `ext y`."
    intro hs
    ext y
    Hint "The goal is `y ∈ f.range ↔ y ∈ ⊤`. Split with `refine ⟨?_, ?_⟩`."
    refine ⟨?_, ?_⟩
    · -- y ∈ f.range → y ∈ ⊤
      Hint "`y ∈ ⊤` is always true. Introduce the hypothesis and use
      `exact Subgroup.mem_top y`."
      intro _
      exact Subgroup.mem_top y
    · -- y ∈ ⊤ → y ∈ f.range
      Hint "Given `y ∈ ⊤` (which is trivially true), show `y ∈ f.range`.
      Unfold range membership and use surjectivity.

      `intro _; rw [MonoidHom.mem_range]; exact hs y`."
      intro _
      rw [MonoidHom.mem_range]
      exact hs y

Conclusion
"
Congratulations on completing the **Homomorphism Problem Set**!

You proved the dual of the Kernel and Image boss:

> **A group homomorphism is surjective if and only if its range
> is the whole group.**

The two fundamental equivalences together:

| Property | Algebraic condition | Subgroup condition |
|----------|--------------------|--------------------|
| **Injective** | `f a = f b → a = b` | `ker(f) = ⊥` |
| **Surjective** | `∀ y, ∃ x, f x = y` | `range(f) = ⊤` |

And the proof structures are duals:
- The `ker = ⊥` proof used `mem_bot` to convert between `x ∈ ⊥` and `x = 1`.
- The `range = ⊤` proof used `mem_top` to convert between `y ∈ ⊤` and `True`.

A homomorphism that is both injective and surjective is an **isomorphism** —
a perfect structural match between two groups. You'll formalize isomorphisms
later in the course.

Your skills from these three worlds:

| Move | Pattern |
|------|---------|
| **Hom-property** | Push `f` through with `map_mul`, `map_one`, `map_inv` |
| **Kernel reasoning** | `rw [mem_ker]` → algebra → `f x = 1` |
| **Image reasoning** | `obtain` witness → `use` new witness → verify |
| **Kernel navigation** | `mem_ker ↔ f x = 1`, `mem_bot ↔ x = 1`, `ker = ⊥` |
| **Range navigation** | `mem_range ↔ ∃ x, f x = y`, `mem_top ↔ True`, `range = ⊤` |

On paper: *Forward: if `range(f) = G`, then for any `y`,
`y ∈ range(f) = G`, so there exists `x` with `f(x) = y`.
Backward: if `f` is surjective, then for any `y`, there exists
`x` with `f(x) = y`, i.e., `y ∈ range(f)`, so `range(f) = G`.*

What's next: you'll study how homomorphisms interact with
composition — does the composition of two injective homomorphisms
remain injective? What about surjective ones?
"
