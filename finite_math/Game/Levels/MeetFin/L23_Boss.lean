import Game.Metadata

World "MeetFin"
Level 23

Title "Boss: Fin Fundamentals"

Introduction "
# Boss: Putting It All Together

Time to combine everything you've learned in a two-part challenge.

**Part 1** — *Transitivity through extensionality*: If `x` and `y`
have the same value, and `y = z` as Fin elements, then `x = z`. This
combines `ext` on the goal (Level 15) with `rw [Fin.ext_iff] at h`
on hypotheses (Level 7).

**Part 2** — *Non-triviality*: Fin 3 has more than one element.
This requires exhaustive case analysis (Levels 16–18), existential
witnesses (Level 22), inequality proving (Level 21), and the Fin
contradiction pattern (Level 13) for the impossible branch.

The boss tests whether you can assemble these moves into a
coherent proof. No single level taught all of this at once.
"

/-- Fin equality is transitive through values, and Fin 3 is non-trivial. -/
Statement : (∀ x y z : Fin 3, x.val = y.val → y = z → x = z) ∧
            (∀ x : Fin 3, ∃ y : Fin 3, x ≠ y) := by
  Hint "The goal is a conjunction. Use `constructor` to split it
  into two sub-goals."
  constructor
  -- Part 1: transitivity through extensionality
  · Hint "Start with `intro x y z h1 h2`."
    intro x y z h1 h2
    Hint "You need to show `x = z`. Use `ext` to convert this to
    a value equality `x.val = z.val`."
    ext
    Hint "Now you need `x.val = z.val`. Use `rw [Fin.ext_iff] at h2`
    to extract `y.val = z.val` from `{h2}`."
    rw [Fin.ext_iff] at h2
    Hint "Now `{h1}` says `x.val = y.val` and `{h2}` says
    `y.val = z.val`. `omega` can chain these."
    omega
  -- Part 2: non-triviality via exhaustive case analysis
  · Hint "Perform exhaustive case analysis: destructure `x` with
    `cases`, then split on the value. For each valid case (0, 1, 2),
    choose a different `Fin 3` element as witness and prove inequality
    with `intro h; cases h`. The impossible case (value >= 3) closes
    with `absurd`."
    intro x
    Hint (hidden := true) "Destructure `x`: `cases x with | mk v hv =>`"
    cases x with
    | mk v hv =>
      Hint (hidden := true) "Case-split on `v`:
      `cases v with | zero => ... | succ n => ...`"
      cases v with
      | zero =>
        Hint (hidden := true) "The element is `0`. Provide `1` as witness:
        `use ⟨1, by omega⟩`, then prove `0 ≠ 1` with `intro h; cases h`."
        use ⟨1, by omega⟩
        intro h
        cases h
      | succ n =>
        Hint (hidden := true) "The element has value `n + 1`. Split on `n`."
        cases n with
        | zero =>
          Hint (hidden := true) "The element is `1`. Use `⟨0, by omega⟩`
          as witness, then `intro h; cases h`."
          use ⟨0, by omega⟩
          intro h
          cases h
        | succ m =>
          Hint (hidden := true) "The element has value `m + 2`. Split on `m`."
          cases m with
          | zero =>
            Hint (hidden := true) "The element is `2`. Use `⟨0, by omega⟩`
            as witness, then `intro h; cases h`."
            use ⟨0, by omega⟩
            intro h
            cases h
          | succ k =>
            Hint (hidden := true) "Here `v = k + 3` but `hv` says `v < 3`.
            This is impossible: `exact absurd hv (by omega)`."
            exact absurd hv (by omega)

Conclusion "
Congratulations — you've completed **Meet Fin**!

You now have these core moves for working with `Fin n`:

| Move | Tool | Learned in |
|---|---|---|
| Construct a `Fin n` element | `⟨k, by omega⟩` | Level 1 |
| Extract the number / coercion | `.val`, `.isLt`, `↑i` | Level 2 |
| Upper bound proof | `.isLt` + `omega` | Level 3 |
| Combine bounds from multiple elements | multiple `.isLt` + `omega` | Level 4 |
| Prove `Fin` elements equal | `rw [Fin.ext_iff]` or `ext` | Levels 5, 15 |
| Rewrite hypotheses | `rw [...] at h` | Levels 7–8 |
| Derive Fin.eta | `rw [Fin.ext_iff]; rfl` | Level 10 |
| Proof irrelevance | `Fin.ext_iff` + `omega` | Level 11 |
| General `Fin (n+1)` reasoning | `.isLt` + `omega` | Level 12 |
| Fin contradiction pattern | `.isLt` + `omega` on empty/impossible | Level 13 |
| Handle `Fin 1` (singleton) | `ext` + `omega` | Level 15 |
| Destructure and case-split | `cases` (nested) + `absurd` | Levels 16–18 |
| Modular arithmetic | construction + `rfl` | Level 19 |
| Use Fin as a concrete index | case analysis on indexed data | Level 20 |
| Prove `Fin` inequality | `intro h; cases h` | Level 21 |
| Existential witness | `use ⟨k, by omega⟩` | Level 22 |

**Where this is going**: `Fin n` is the *canonical* finite type in
Lean — the standard model that everything connects back to. Every
finite type with `n` elements is equivalent to `Fin n`, making it
the universal representative. A function `Fin n → α` is essentially
an `n`-tuple: an ordered list of `n` elements from `α`. You'll
explore this idea in the FinTuples world.

Beyond tuples, you'll meet `Finset` (unordered finite collections),
`Fintype` (types with finitely many elements), and big operators
like `∑` and `∏` over finite index sets. All of these are built on
the foundation you've just learned.

(As you saw in Level 19, `Fin n` also carries modular arithmetic —
addition and multiplication wrap around mod `n`, making `Fin n` a
model of `ℤ/nℤ`. This course focuses on `Fin` as a finite index
type, not as a number system.)

In the next world, you'll learn to **navigate** within `Fin n` —
moving forward with `Fin.succ`, embedding with `Fin.castSucc`, and
reaching the boundary with `Fin.last`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
