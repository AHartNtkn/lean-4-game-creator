import Game.Levels.PsetImgPreimg.L01_ImageSubsetRange
import Game.Levels.PsetImgPreimg.L02_ConcreteComputation
import Game.Levels.PsetImgPreimg.L03_ImageInterPreimage
import Game.Levels.PsetImgPreimg.L04_ImageIndexedInterSubset
import Game.Levels.PsetImgPreimg.L05_ImageIndexedUnion
import Game.Levels.PsetImgPreimg.L06_ImageDiffSubset
import Game.Levels.PsetImgPreimg.L07_InjectiveInterImage
import Game.Levels.PsetImgPreimg.L08_InjectiveIndexedInterImage
import Game.Levels.PsetImgPreimg.L09_InjectiveDiffImage
import Game.Levels.PsetImgPreimg.L10_Boss

World "PsetImgPreimg"
Title "Problem Set: Images & Preimages"

Introduction "
# Problem Set: Images & Preimages

You have completed Preimage World and Image World. Time to test those
skills on fresh problems.

**What you learned**:
- **Preimage**: `f ⁻¹' t` is the set of `x` with `f x ∈ t`. Membership
  is function application. Preserves ALL set operations.
- **Image**: `f '' s` is the set of `y` such that some `x ∈ s` has
  `f x = y`. Membership requires a witness. Preserves unions, but
  only ⊆ for intersections.
- **Power tools**: `rintro ⟨x, hx, rfl⟩`, `obtain`, `rcases` for
  destructuring. Anonymous constructors `⟨x, hx, rfl⟩` for building
  image/range membership.
- **The gaps**: `f '' (f ⁻¹' t) ⊆ t` (equality needs surjectivity).
  `s ⊆ f ⁻¹' (f '' s)` (equality needs injectivity).

**What to expect**:
- Level 1: Image subset of range (warmup)
- Level 2: Concrete image computation (grounding the abstraction)
- Level 3: Image meets preimage — a clean equality (combining both)
- Level 4: Image of indexed intersection (extending to indexed ops)
- Level 5: Image of indexed union — equality! (the missing cell)
- Level 6: Image and set difference (needs contradiction reasoning)
- Level 7: Injectivity closes the binary intersection gap (new concept)
- Level 8: Injectivity closes the indexed intersection gap
- Level 9: Injectivity makes set difference an equality (combining L6 + L7)
- Level 10 (Boss): Injectivity closes the preimage-image gap

**New concept**: Levels 7–10 use `Function.Injective f`, which says
`∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂`. This concept is explored fully in
Injective World — here you use it as a tool to close the gaps you
discovered in Image World.

Hints are sparser than in lecture worlds. Trust your skills.
"
