import Game.Metadata

World "CommGroupIntro"
Level 2

Title "Rearranging with Commutativity"

Introduction
"
When you write `rw [mul_comm]`, Lean swaps the first `_ * _` it
finds. With three or more factors, you need to **target** which
pair to swap by providing arguments: `rw [mul_comm a b]` swaps
`a` and `b` specifically, leaving other factors alone.

**Your task**: rearrange `a * b * c` to `c * b * a`.

Remember that `a * b * c` means `(a * b) * c` (left association).
You'll need to combine `mul_comm` with `mul_assoc` to move
factors around.

**Strategy**: Think of this in two stages:
1. Swap `(a * b)` with `c` to get `c * (a * b)`
2. Swap `a` with `b` inside the parentheses
3. Remove the parentheses with `mul_assoc`
"

/-- `mul_left_comm` says `a * (b * c) = b * (a * c)` — it swaps
`a` past `b` when `a` is on the far left of `a * (b * c)`.

This is a convenience lemma derived from `mul_comm` and `mul_assoc`.
Useful when you want to permute the first two factors of a
right-associated triple. -/
TheoremDoc mul_left_comm as "mul_left_comm" in "Group"

NewTheorem mul_left_comm

TheoremTab "Group"

Statement (G : Type*) [CommGroup G] (a b c : G) :
    a * b * c = c * b * a := by
  Hint "You need to rearrange `a * b * c` to `c * b * a`. The key
  skill: provide arguments to `mul_comm` to target specific swaps.

  Try `rw [mul_comm (a * b) c]` to swap `(a * b)` with `c`.
  Then swap `a` and `b`."
  Hint (hidden := true) "After `rw [mul_comm (a * b) c]`, the goal
  becomes `c * (a * b) = c * b * a`. Now use `rw [mul_comm a b]`
  to swap `a` and `b`, giving `c * (b * a) = c * b * a`. Finally
  `rw [← mul_assoc]` removes the parentheses."
  Branch
    -- calc proof
    calc a * b * c
        _ = c * (a * b)  := by rw [mul_comm (a * b) c]
        _ = c * (b * a)  := by rw [mul_comm a b]
        _ = c * b * a    := by rw [← mul_assoc]
  Branch
    -- Using group tactic (note: group handles CommGroup too)
    group
  rw [mul_comm (a * b) c, mul_comm a b, ← mul_assoc]

Conclusion
"
The key technique here is **targeted rewriting**: `rw [mul_comm a b]`
provides arguments to select *which* `_ * _` to rewrite. Without
arguments, `mul_comm` swaps the first match Lean finds, which may
not be what you want. You used targeted rewrites with `mul_assoc`
in earlier worlds; from here on, you'll use them constantly with
`mul_comm` as well.

A convenience lemma is now in your inventory:

| Theorem | Statement |
|---------|-----------|
| `mul_left_comm` | `a * (b * c) = b * (a * c)` |

This is derived from `mul_comm` and `mul_assoc`, and saves
multi-step rearrangements when you need to permute the first two
factors of a right-associated triple. It only works in commutative
groups (or commutative semigroups).
"
