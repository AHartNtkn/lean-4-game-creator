import Game.Levels.GroupBasics.L01_DeriveLeftInverse
import Game.Levels.GroupBasics.L02_DeriveLeftIdentity
import Game.Levels.GroupBasics.L03_InvMulCancelLeft
import Game.Levels.GroupBasics.L04_MulInvCancelLeft
import Game.Levels.GroupBasics.L05_LeftCancel
import Game.Levels.GroupBasics.L06_RightCancel
import Game.Levels.GroupBasics.L07_InverseUniqueness
import Game.Levels.GroupBasics.L08_InvInv
import Game.Levels.GroupBasics.L09_Boss

World "GroupBasics"
Title "Derived Theorems"

Introduction
"
Welcome to **Group Basics**, where you'll see the real power of the
three group axioms.

In the Group Tutorial, you used five tools: `mul_assoc`, `mul_one`,
`one_mul`, `mul_inv_cancel`, and `inv_mul_cancel`. But only three of
these are truly independent:

1. **Associativity**: `mul_assoc`
2. **Right identity**: `mul_one`
3. **Right inverse**: `mul_inv_cancel`

Everything else — left identity, left inverse, cancellation laws,
uniqueness of inverses — can be **derived** from these three. That's
what this world is about. Minimizing axioms isn't pedantry — it means
less to verify when checking that a new structure is a group.

Along the way, you'll build a toolkit of cancellation lemmas that
make group algebra much faster than raw axiom manipulation.

**Note**: The `group` tactic is **disabled** for this entire world.
You need to prove everything from the axioms and the theorems you
derive. `group` will return in the next world.

By the end of this world, you'll prove the **shoes-and-socks lemma**:

$(a * b)^{-1} = b^{-1} * a^{-1}$

— the inverse of a product is the product of the inverses in reverse
order.
"
