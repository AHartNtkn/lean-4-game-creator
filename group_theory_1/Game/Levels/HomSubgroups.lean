import Game.Levels.HomSubgroups.L01_ComapDef
import Game.Levels.HomSubgroups.L02_ComapMulMem
import Game.Levels.HomSubgroups.L03_MapDef
import Game.Levels.HomSubgroups.L04_MapMulMem
import Game.Levels.HomSubgroups.L05_KernelAsPreimage
import Game.Levels.HomSubgroups.L06_MapComapLe
import Game.Levels.HomSubgroups.L07_Boss

World "HomSubgroups"
Title "Homomorphism Subgroups"

Introduction
"
If `f : G →* H` is a homomorphism and `K` is a subgroup of `H`, what
can we say about the set `f⁻¹(K) = {x ∈ G | f(x) ∈ K}`?

It's a subgroup of `G`. The proof is almost automatic: since `K` is
closed under multiplication, inverses, and contains the identity, and
since `f` preserves all of these, the preimage inherits all three
closure properties. Lean calls this subgroup `Subgroup.comap f K`
(\"contravariant map\" — it goes backward, from `H` to `G`).

Similarly, if `K` is a subgroup of `G`, then `f(K) = {f(x) | x ∈ K}`
is a subgroup of `H`. Lean calls this `Subgroup.map f K` (\"covariant
map\" — it goes forward).

These two operations — `comap` (preimage) and `map` (image) —
generalize the kernel and range you already know:
- `ker(f) = comap f ⊥` (preimage of the trivial subgroup)
- `range(f) = map f ⊤` (image of the whole group)

In this world you'll learn to reason about `comap` and `map`
membership, prove the kernel-as-preimage connection, and show that
`map` and `comap` are related by a Galois connection:

> **`map f K ≤ L  ↔  K ≤ comap f L`**
"
