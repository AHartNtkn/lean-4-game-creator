import Game.Metadata

World "SurjectiveWorld"
Level 12

Title "Counterexample: Surjective g ∘ f, Non-Surjective f"

TheoremTab "Function"

Introduction "
# The False Converse: A Concrete Counterexample

In Level 10, you proved that `Surjective (g ∘ f) → Surjective g` — the
outer function inherits surjectivity. The conclusion noted that the
converse for `f` is FALSE.

Now prove it with functions you already know:

- `f = fun n : ℕ => 2 * n` — the doubling function (NOT surjective, Level 2)
- `g = fun n : ℕ => n / 2` — the halving function (surjective, Level 4)
- `g ∘ f = fun n => (2 * n) / 2 = n` — the identity (surjective!)

The composition `g ∘ f` is surjective because `g` \"undoes\" `f`, but `f`
alone misses all odd numbers.

**Your task**: Prove BOTH parts:
1. `Surjective (g ∘ f)` — the composition is surjective
2. `¬ Surjective f` — `f` alone is not surjective
"

/-- The composition of halving after doubling is surjective,
but doubling alone is not. -/
Statement : (Function.Surjective ((fun n : ℕ => n / 2) ∘ (fun n : ℕ => 2 * n))) ∧
    ¬ Function.Surjective (fun n : ℕ => 2 * n) := by
  Hint "The goal is a conjunction. Split it with `constructor`."
  constructor
  -- Part 1: g ∘ f is surjective
  · Hint "Prove `Surjective ((fun n => n / 2) ∘ (fun n => 2 * n))`.
    The composition simplifies to `fun n => (2 * n) / 2 = n`.

    Start with `intro b` as always."
    intro b
    Hint "You need `a` with `(2 * a) / 2 = b`. Since `(2 * b) / 2 = b`,
    the witness is `b` itself. Use `use b`."
    Hint (hidden := true) "`use b`."
    use b
    Hint "The goal is `((fun n => n / 2) ∘ (fun n => 2 * n)) b = b`,
    which is `(2 * b) / 2 = b`. Use `show 2 * b / 2 = b` to make the
    arithmetic explicit, then `omega`."
    Hint (hidden := true) "`show 2 * b / 2 = b` then `omega`."
    show 2 * b / 2 = b
    omega
  -- Part 2: f is NOT surjective
  · Hint "Prove `¬ Surjective (fun n => 2 * n)`. This is the same as
    Level 2! Assume surjectivity with `intro h`, apply it to `1`, and
    derive a contradiction."
    intro h
    Hint "Apply `h` to `1` — the element with no preimage under doubling.
    Use `obtain ⟨a, ha⟩ := h 1`."
    Hint (hidden := true) "`obtain ⟨a, ha⟩ := h 1`."
    obtain ⟨a, ha⟩ := h 1
    Hint "You have `ha : 2 * a = 1` (possibly wrapped in a lambda).
    No natural number satisfies this. Create the explicit equation:
    `have ha' : 2 * a = 1 := ha`
    then use `omega`."
    Hint (hidden := true) "`have ha' : 2 * a = 1 := ha` then `omega`."
    Branch
      change 2 * a = 1 at ha
      Hint "The goal is `False` and you have `ha : 2 * a = 1`. No natural
      number satisfies this — `omega` can close the goal."
      omega
    have ha' : 2 * a = 1 := ha
    omega

Conclusion "
You proved a concrete counterexample to the false converse!

| Statement | True? | Proof |
|---|---|---|
| `Surjective (g ∘ f) → Surjective g` | YES (Level 10) | Witness transfer |
| `Surjective (g ∘ f) → Surjective f` | NO (this level) | Counterexample |

**Why this works**: `g = n / 2` is surjective and \"covers\" for the
non-surjective `f = 2 * n`. The composition `g ∘ f` acts like the
identity, so it is surjective — but `f` alone misses all odd numbers.

**The retrieval pattern**: The second part reproved Level 2's result.
Seeing the same proof shape in a new context reinforces the pattern:
find a missing output, apply the assumed surjectivity to it, contradict.

**Contrast with injectivity**: In Injective World, you proved a similar
false converse: `Injective (g ∘ f)` does NOT imply `Injective g`.
The asymmetry: composition preserves the inner function's injectivity
and the outer function's surjectivity, but not vice versa.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.Surjective.of_comp
