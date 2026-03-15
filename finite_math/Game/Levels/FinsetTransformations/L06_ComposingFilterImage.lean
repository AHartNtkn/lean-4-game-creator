import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 6

Title "Composing filter and image"

Introduction
"
# Filter then image

Now that you know both `filter` and `image`, let's compose them.
A common pattern is: **filter** a finset to select elements of
interest, then **map** a function over the result.

## Your task

Starting from {1, 2, 3, 4, 5}:

1. **Filter** to keep only the odd numbers: {1, 3, 5}.
2. **Apply** the doubling function `(· * 2)`: {2, 6, 10}.

Prove that `6` belongs to the result.

**Strategy**: Rewrite with `Finset.mem_image` to see the existential
in the outer operation. The witness is `3` (since `3 * 2 = 6`).
Then you need to show `3` belongs to the filtered finset, which
requires `Finset.mem_filter`.
"

/-- `6` is in the image of the odd elements of {1,2,3,4,5} under doubling. -/
Statement : (6 : Nat) ∈ Finset.image (· * 2)
    (Finset.filter (fun x => x % 2 = 1) ({1, 2, 3, 4, 5} : Finset Nat)) := by
  Hint "The outermost operation is `image`. Start by rewriting with
  `Finset.mem_image`."
  Hint (hidden := true) "Use `rw [Finset.mem_image]`."
  rw [Finset.mem_image]
  Hint "Provide the witness: which odd number from the source finset
  doubles to `6`?"
  Hint (hidden := true) "Use `use 3`."
  use 3
  Hint "Now you need to show that `3` is in the filtered finset and
  that `3 * 2 = 6`. Split with `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "For the filter membership, use `Finset.mem_filter` to split
    into membership and predicate."
    Hint (hidden := true) "Use `rw [Finset.mem_filter]` then `constructor`."
    rw [Finset.mem_filter]
    constructor
    · simp [Finset.mem_insert, Finset.mem_singleton]
    · rfl
  · Hint "The equation `3 * 2 = 6` is a computation."
    Hint (hidden := true) "Use `rfl` or `norm_num`."
    rfl

Conclusion
"
You composed `filter` and `image` by peeling off the operations
from the outside in:

1. **Outer** operation is `image` → use `mem_image` first.
2. **Inner** operation is `filter` → use `mem_filter` inside.

This \"outside-in\" strategy works for any nesting of finset
operations. Always start with the outermost operation's membership
lemma.

## The dual composition

You could also **image then filter**: apply a function first, then
select from the result. The proof shape would be different -- you
would start with `mem_filter` (since filter is outermost), then
handle the image membership inside. The lemma
`Finset.filter_image` relates the two compositions:

```
filter p (image f s) = image f (filter (p ∘ f) s)
```
"

DisabledTactic trivial decide native_decide aesop simp_all
