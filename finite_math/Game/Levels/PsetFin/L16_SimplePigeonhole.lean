import Game.Metadata

World "PsetFin"
Level 16

Title "Simple Pigeonhole: Two Pigeons, One Hole"

Introduction "
# The Simplest Pigeonhole

The **pigeonhole principle** says: if you have $n+1$ pigeons
and only $n$ pigeonholes, at least two pigeons must share a hole.
The name comes from the image of pigeons roosting: with more
birds than holes, some hole gets crowded.

More precisely: any function $f : A \\to B$ with $|A| > |B|$
fails to be injective — there exist distinct $i, j \\in A$ with
$f(i) = f(j)$.

Before tackling the full 3-pigeons-2-holes version, let's practice
the pattern on the simplest case: **2 pigeons, 1 hole**.

Any function `f : Fin 2 -> Fin 1` must send two different inputs
to the same output. Why? Because `Fin 1` has only ONE element
(the value `0`), so both `f 0` and `f 1` must equal `0`.

**Strategy**:
1. The witnesses are `0` and `1` (the two inputs)
2. They're different (the inequality `0 /= 1`)
3. Both map to the unique output

The 'classify + compare' pattern:
- Every `Fin 1` element is `0` (classify)
- So `f 0 = 0` and `f 1 = 0` (compare)
- Therefore `f 0 = f 1` (collision found)
"

/-- Any function from Fin 2 to Fin 1 has a collision. -/
Statement (f : Fin 2 → Fin 1) : ∃ i j : Fin 2, i ≠ j ∧ f i = f j := by
  Hint "Every `Fin 1` element has value `0` (since `v < 1` forces `v = 0`).
  First classify `f 0` and `f 1`:
  `have h0 : f 0 = 0 := by ext; omega`"
  Hint (hidden := true) "`have h0 : f 0 = 0 := by ext; omega` gives
  `f 0 = 0` (the only possible value). Similarly for `f 1`.
  Then `use 0, 1`."
  have h0 : f 0 = 0 := by ext; omega
  have h1 : f 1 = 0 := by ext; omega
  Hint "Now provide the witnesses. `use 0, 1` says: the collision
  is between inputs `0` and `1`."
  use 0, 1
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "Prove `(0 : Fin 2) /= 1`. Use the inequality pattern:
    `intro h; cases h`."
    intro h; cases h
  · Hint "Prove `f 0 = f 1`. Rewrite both sides using `h0` and `h1`."
    Hint (hidden := true) "`rw [h0, h1]`"
    rw [h0, h1]

Conclusion "
The simplest pigeonhole: with only ONE hole, every pigeon goes in
the same place.

The proof pattern was:
1. **Classify**: show every output is `0` (the only `Fin 1` element)
2. **Provide witnesses**: `use 0, 1`
3. **Prove inequality**: `intro h; cases h`
4. **Prove collision**: rewrite both outputs to `0`

This is the same 'classify + compare' pattern that scales to
3-pigeons-2-holes — which is your next challenge. The difference:
with 2 holes, the classification has branches (each output is `0`
or `1`), so you'll need a case tree instead of a single path.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
