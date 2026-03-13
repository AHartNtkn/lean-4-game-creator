import Game.Metadata

World "HomPset"
Level 5

Title "Powers in the Kernel"

Introduction
"
If `f(a) = 1`, what about `f(a²)`, `f(a³)`, or `f(aⁿ)` in general?

Since `f(aⁿ) = f(a)ⁿ = 1ⁿ = 1`, every power of `a` also maps to `1`.

Prove this by induction on `n`.

**Base case** (`n = 0`): `f(a⁰) = f(1) = 1` by `pow_zero` and `map_one`.

**Inductive step** (`n → n+1`): `f(aⁿ⁺¹) = f(aⁿ · a) = f(aⁿ) · f(a) = 1 · 1 = 1`
using `pow_succ`, `map_mul`, the inductive hypothesis, and `h`.
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem map_pow map_zpow

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a : G)
    (h : f a = 1) (n : ℕ) : f (a ^ n) = 1 := by
  Hint "Use `induction n with` to set up base and inductive cases.

  The syntax is:
  ```
  induction n with
  | zero => ...
  | succ n ih => ...
  ```"
  induction n with
  | zero =>
    Hint "The goal is `f (a ^ 0) = 1`. Use `rw [pow_zero]` to simplify
    `a ^ 0` to `1`, then `rw [map_one]` to close."
    rw [pow_zero, map_one]
  | succ n ih =>
    Hint "The inductive hypothesis is `{ih} : f (a ^ n) = 1`.
    The goal is `f (a ^ (n + 1)) = 1`.

    Expand `a ^ (n + 1)` with `rw [pow_succ]` to get `f (a ^ n * a) = 1`."
    rw [pow_succ]
    Hint "Push `f` through: `rw [map_mul]`."
    rw [map_mul]
    Hint "Substitute the inductive hypothesis, simplify `1 * _`, and
    use `{h}`: `rw [{ih}, one_mul, {h}]`."
    Branch
      rw [ih, h, one_mul]
    rw [ih, one_mul, h]

Conclusion
"
Every power of a kernel element is again in the kernel.

The proof combined **induction** (from Commutative Groups) with
the **hom-property move**. The key step was recognizing that
`pow_succ` reduces `aⁿ⁺¹` to `aⁿ · a`, which lets you apply
`map_mul` and use the inductive hypothesis.

On paper: *By induction. Base: `f(a⁰) = f(1) = 1`. Step: if
`f(aⁿ) = 1`, then `f(aⁿ⁺¹) = f(aⁿ · a) = f(aⁿ)f(a) = 1 · 1 = 1`.*

This result also follows immediately from `map_pow`: `f(aⁿ) = f(a)ⁿ = 1ⁿ = 1`.
But the manual induction proof shows *why* `map_pow` is true — it's
the same `map_mul` argument repeated `n` times.

The same holds for integer powers `a ^ (z : ℤ)`: since the kernel
is closed under inverses, negative powers also stay in the kernel.
"
