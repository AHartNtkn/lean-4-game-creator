import GameServer.Commands
import Mathlib

World "FinIntro"
Level 4

Title "The round-trip"

Introduction
"
# `Fin.mk` and `Fin.val` are inverses

You have learned two operations:
- `Fin.mk val proof` constructs a `Fin n` element from a number and a proof
- `i.val` extracts the number from a `Fin n` element

These are inverses. If you start with `i : Fin n`, extract its value `i.val`
and its proof `i.isLt`, and then reconstruct `Fin.mk i.val i.isLt`, you
get `i` back.

This round-trip identity says: a `Fin n` element is *nothing more* than a
natural number with a proof of boundedness. There is no hidden data -- you
can always take it apart and put it back together.

## Your task

Prove that `Fin.mk i.val i.isLt = i` for an arbitrary `i : Fin 4`.

Use `ext` to reduce to an equality of values. After `ext`, the goal
becomes `(Fin.mk i.val i.isLt).val = i.val`, which simplifies to
`i.val = i.val`.
"

/-- Reconstructing a `Fin` element from its parts gives back the original. -/
Statement (i : Fin 4) : Fin.mk i.val i.isLt = i := by
  Hint "Use `ext` to reduce to showing the underlying values are equal."
  ext
  Hint "The goal is `i.val = i.val`. This is true by `rfl`."
  rfl

Conclusion
"
The round-trip works: tearing a `Fin n` element apart and reassembling it
gives back the original.

This crystallizes the subtype structure. A `Fin n` element is *exactly*
a natural number together with a proof -- no more, no less. You can always
reconstruct one from its `.val` and `.isLt`, and you will always get back
what you started with.

This pattern -- constructor and destructor as inverses -- appears throughout
Lean's type theory. For `Fin n`, the key pair is:
- **Constructor**: `Fin.mk val proof` builds the element
- **Destructors**: `.val` and `.isLt` extract the parts

Understanding this will help in later worlds when you need to build `Fin`
elements from computed values or destruct them to reason about their parts.
"
