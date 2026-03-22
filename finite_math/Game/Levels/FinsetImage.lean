import Game.Levels.FinsetImage.L01_FirstContactWithImage
import Game.Levels.FinsetImage.L02_ChoosingTheWitness
import Game.Levels.FinsetImage.L03_NotInTheImage
import Game.Levels.FinsetImage.L04_ImageGrowsWithTheSet
import Game.Levels.FinsetImage.L05_ImageDistributes
import Game.Levels.FinsetImage.L06_ImageUnionEquality
import Game.Levels.FinsetImage.L07_ImageComposition
import Game.Levels.FinsetImage.L08_ImageOfSingleton
import Game.Levels.FinsetImage.L09_ImageIntersectionSubset
import Game.Levels.FinsetImage.L10_ImageIntersectionCounterexample
import Game.Levels.FinsetImage.L11_ConstantFunctionForward
import Game.Levels.FinsetImage.L12_PartialCollapse
import Game.Levels.FinsetImage.L13_ConstantImageEquality
import Game.Levels.FinsetImage.L14_ImageCanOnlyShrink
import Game.Levels.FinsetImage.L15_InjectivePreservesSize
import Game.Levels.FinsetImage.L16_ProvingInjectivity
import Game.Levels.FinsetImage.L17_WhyInjectivityMatters
import Game.Levels.FinsetImage.L18_ImageIntersectionEquality
import Game.Levels.FinsetImage.L19_CardPreservationConverse
import Game.Levels.FinsetImage.L20_ReverseRewriting
import Game.Levels.FinsetImage.L21_CountingProvesInjectivity
import Game.Levels.FinsetImage.L22_ShowTactic
import Game.Levels.FinsetImage.L23_Boss

World "FinsetImage"
Title "Finset Image"

Introduction "
# Finset Image: Applying Functions to Sets

You know how to build finsets and prove membership, union,
intersection, and equality. But functions acting on sets are
central to mathematics: image, preimage, injectivity.

This world covers `Finset.image f s` — the finset of all values
`f x` for `x ∈ s`. The key membership characterization:

$$y \\in f(S) \\;\\longleftrightarrow\\; \\exists x \\in S,\\; f(x) = y$$

In Lean: `Finset.mem_image : y ∈ s.image f ↔ ∃ x ∈ s, f x = y`

The proof moves split into two directions:
- **Forward** (proving membership): provide a witness `x ∈ s` with `f x = y`
- **Backward** (using a membership hypothesis): extract the witness
  with `obtain ⟨x, hx, hfx⟩`

The first half covers membership, boundary cases (singleton
images), distributivity over union, image of intersections,
and the effect of non-injective functions (both total collapse
via constant functions and partial collapse).

The second half introduces **cardinality** (`s.card`)
and the fundamental relationship between images and injectivity:
- Non-injective functions shrink: collisions reduce cardinality
- Image can only shrink: `card_image_le` says $|f(S)| \\leq |S|$
- Injective functions preserve size: `card_image_of_injective` says
  $f$ injective implies $|f(S)| = |S|$
- Injectivity repairs intersection: $f$ injective implies
  $f(S \\cap T) = f(S) \\cap f(T)$
- The converse holds too: `card_image_iff` gives the equivalence
  $|f(S)| = |S| \\iff f$ is injective on $S$

The boss combines forward membership, backward extraction
(for subset bounds), and cardinality preservation via injectivity.
"
