import Game.Levels.HomBasics.L01_KernelDef
import Game.Levels.HomBasics.L02_SpecializeTactic
import Game.Levels.HomBasics.L03_KernelPractice
import Game.Levels.HomBasics.L04_RangeDef
import Game.Levels.HomBasics.L05_RangePractice
import Game.Levels.HomBasics.L06_InjectiveKernel
import Game.Levels.HomBasics.L07_TrivialKernelEquals
import Game.Levels.HomBasics.L08_Boss

World "HomBasics"
Title "Kernel and Image"
Introduction
"
Welcome to **Kernel and Image**.

In the last world, you learned to push a homomorphism through group
operations: `f(ab) = f(a)f(b)`, `f(1) = 1`, `f(a⁻¹) = f(a)⁻¹`.
You ended by showing that `f(a) = f(b)` implies `f(ab⁻¹) = 1`.

That calculation revealed something important: the set
`ker(f) = {x ∈ G | f(x) = 1}` captures exactly how much information
`f` loses. Elements in the kernel are \"invisible\" to `f` — they all
get mapped to the identity.

The **kernel** of a homomorphism is always a subgroup: it contains `1`,
is closed under multiplication, and is closed under inverses. In Lean,
`f.ker` is a `Subgroup G`.

At the other end, the **range** (or image) of `f` is the set of elements
in `H` that `f` actually reaches: `range(f) = {y ∈ H | ∃ x, f(x) = y}`.
This is also a subgroup, written `f.range`.

The central question of this world: **when does `f` lose no information?**
A homomorphism is injective exactly when its kernel is trivial — when
`ker(f) = {1}`. If the only element that maps to `1` is `1` itself, then
distinct inputs always produce distinct outputs.

You will prove both directions of this equivalence and combine them into
the boss theorem: `ker f = ⊥ ↔ f injective`.

Along the way, you'll learn the `specialize` tactic, which lets you
pin a universal hypothesis to a specific element.
"
