import Game.Metadata

World "MeetFin"
Level 19

Title "Modular Arithmetic"

Introduction "
# Enrichment: Fin Has Arithmetic

*This level is an enrichment aside — a mathematical surprise that
connects `Fin n` to a different area of mathematics. The main course
path resumes in the next level.*

You've been treating `Fin n` as an index set — a collection of
positions `0, 1, ..., n-1`. But `Fin n` also supports **arithmetic**,
and it works differently from natural number arithmetic.

What is `3 + 4` in `Fin 5`? On natural numbers, it's `7`. But `Fin 5`
only has elements `0, 1, 2, 3, 4` — there is no `7`. Addition on
`Fin n` **wraps around**: it takes the result modulo `n`.

So `(3 : Fin 5) + (4 : Fin 5) = (2 : Fin 5)` because `7 mod 5 = 2`.
This is **modular arithmetic** — the arithmetic of clocks, cyclic
groups, and the integers mod `n`.

**Your task**: Find two elements `a, b : Fin 5` such that
`a + b = 0` (their sum wraps around to zero) and their natural
number values sum to `5`.

(Hint: on a 5-hour clock, which two different hours are diametrically
opposite — summing to a full rotation?)
"

/-- Find two Fin 5 elements that sum to 0 modularly and to 5 naturally. -/
Statement : ∃ a b : Fin 5, a + b = 0 ∧ a.val + b.val = 5 := by
  Hint "Provide both witnesses with `use`.
  Which two numbers less than 5 sum to 5 as naturals and to 0 mod 5?"
  Hint (hidden := true) "Try `use ⟨1, by omega⟩, ⟨4, by omega⟩`."
  use ⟨1, by omega⟩, ⟨4, by omega⟩
  Hint "Now prove both parts of the conjunction with `constructor`."
  constructor
  · Hint "The sum `1 + 4` in Fin 5 equals `5 mod 5 = 0`.
    Since this is a definitional computation, `rfl` closes it."
    rfl
  · Hint "The natural sum `1 + 4 = 5`. Since the values are concrete
    numbers, Lean computes the result and `rfl` closes it."
    rfl

Conclusion "
Every nonzero element of `Fin 5` generates the whole group under
repeated addition — after exactly 5 steps, you return to 0. This
is because 5 is prime, making `Fin 5` a **cyclic group** where
every nonzero element is a generator.

More examples of modular arithmetic in `Fin 5`:
- `(3 : Fin 5) + (4 : Fin 5) = 2` (because `7 mod 5 = 2`)
- `(2 : Fin 5) * (3 : Fin 5) = 1` (because `6 mod 5 = 1`)
- `(4 : Fin 5) + (1 : Fin 5) = 0` (because `5 mod 5 = 0`)

Notice that both halves of the conjunction close by `rfl` — both
are *definitional computations*. The modular sum `1 + 4` reduces
to `0` in `Fin 5` because Lean computes `5 mod 5 = 0`. The natural
sum `1 + 4` reduces to `5` because Lean computes `1 + 4 = 5`.
The `constructor` tactic split the conjunction so each half could
be verified independently.

This is the arithmetic of a **clock with `n` hours**: when you pass
the maximum, you wrap back to 0. Mathematically, `Fin n` with this
arithmetic is a model of the integers modulo `n` (written
$\\mathbb{Z}/n\\mathbb{Z}$).

This course focuses on `Fin n` as a finite index type, not as a
number system. But this modular structure appears again sooner than
you might expect. In the Problem Set (PsetFin), you'll prove that
the cyclic permutation `![1, 2, 0] : Fin 3 -> Fin 3` has no fixed
points — every element moves. That permutation cycles
`0 -> 1 -> 2 -> 0`, exactly the same cyclic structure you see here
with addition modulo 5.

When you study `Fintype.card` in the Cardinality world, the fact
that `Fintype.card (Fin n) = n` connects the type-theoretic size
of `Fin n` to this algebraic structure.

Now back to our main path: using `Fin` as an index for concrete data.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Fin.forall_fin_two
