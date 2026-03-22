import Game.Metadata

World "FinNavigation"
Level 16

Title "Boss: The Decomposition"

Introduction "
# Boss: Putting Navigation Together

Time to combine everything. This boss has two parts.

**Part 1 — The Decomposition**: Every element of `Fin 3` is
either `Fin.last 2` or `j.castSucc` for some `j : Fin 2`.

This is the structural heart of `Fin` navigation: `Fin (n+1)`
splits into the `castSucc` images (from `Fin n`) and
`Fin.last n`. No element falls outside these two cases.

Strategy: destructure (Level 16 of MeetFin), case-split on
the value, then use Level 12 (recognizing last) or Level 13
(finding castSucc) for each case.

**Part 2 — Succ injectivity**: You proved this in Level 9.
Here you combine it with the decomposition in a single proof.
The pattern is the same: `ext_iff`, `val_succ`, `ext`, `omega`.
"

/-- The last-or-castSucc decomposition, and succ injectivity. -/
Statement : (∀ i : Fin 3, i = Fin.last 2 ∨ ∃ j : Fin 2, i = j.castSucc) ∧
            (∀ i j : Fin 3, i.succ = j.succ → i = j) := by
  Hint "The goal is a conjunction. Use `constructor` to split it."
  constructor
  -- Part 1: decomposition
  · Hint "Part 1: prove every `Fin 3` element is `last` or `castSucc`.
    Start with `intro i`, then destructure `i` with
    `cases i with | mk v hv =>`."
    intro i
    Hint (hidden := true) "Destructure: `cases i with | mk v hv =>`"
    cases i with
    | mk v hv =>
      Hint "Now `v : ℕ` and `hv : v < 3`. Case-split on `v`:
      `cases v with | zero => ... | succ n => ...`"
      cases v with
      | zero =>
        Hint "Here `v = 0`. This is a `castSucc` image (value `< 2`).
        Choose `right`, then provide the preimage `⟨0, by omega⟩ : Fin 2`,
        then `ext; rw [Fin.val_castSucc]`."
        right
        Hint "To provide the preimage, use `use ⟨i.val, proof⟩` where
        `i.val` is the value and the proof shows it's less than 2.
        Here: `use ⟨0, by omega⟩`."
        Hint (hidden := true) "`use ⟨0, by omega⟩`"
        use ⟨0, by omega⟩
        Hint (hidden := true) "`ext; rw [Fin.val_castSucc]`"
        ext
        rw [Fin.val_castSucc]
      | succ n =>
        Hint (hidden := true) "Case-split on `n`:
        `cases n with | zero => ... | succ m => ...`"
        cases n with
        | zero =>
          Hint (hidden := true) "Here `v = 1`. Still a `castSucc` image.
          `right; use ⟨1, by omega⟩; ext; rw [Fin.val_castSucc]`"
          right
          use ⟨1, by omega⟩
          ext
          rw [Fin.val_castSucc]
        | succ m =>
          Hint (hidden := true) "Split on `m` once more."
          cases m with
          | zero =>
            Hint (hidden := true) "Here `v = 2 = Fin.last 2`. Choose `left`,
            then `ext; rw [Fin.val_last]`."
            left
            ext
            rw [Fin.val_last]
          | succ k =>
            Hint (hidden := true) "Here `v = k + 3` but `hv` says `v < 3`.
            Impossible: `exact absurd hv (by omega)`."
            exact absurd hv (by omega)
  -- Part 2: succ injectivity
  · Hint "Part 2: prove succ is injective. Start with `intro i j h`."
    intro i j h
    Hint "Convert `{h}` to values: `rw [Fin.ext_iff] at h`."
    rw [Fin.ext_iff] at h
    Hint "Simplify succ values: `rw [Fin.val_succ, Fin.val_succ] at h`.
    This gives `i.val + 1 = j.val + 1`."
    rw [Fin.val_succ, Fin.val_succ] at h
    Hint "Now reduce the goal to values with `ext`, and close with `omega`."
    ext
    omega

Conclusion "
Congratulations — you've completed **Fin Navigation**!

**The Decomposition** (Part 1): Every element of `Fin (n+1)` is
either `Fin.last n` or `j.castSucc` for some `j : Fin n`. This
is the `Fin` analog of: every natural number $k \\leq n$ either
equals $n$ or is strictly less than $n$.

Combined with the **separation fact** from Level 7 — that no
`castSucc` image equals `Fin.last` — this gives you a **disjoint
decomposition**: `Fin (n+1)` is the disjoint union of the
`castSucc` images (values $0, \\ldots, n-1$) and the singleton
`Fin.last n` (value $n$). Part 1 gives **exhaustion** (every
element falls into one of the two sets), and Level 7 gives
**disjointness** (no element falls into both). Together:
`Fin (n+1) = image(castSucc) ⊔ {last}`, disjointly.

**Connection to induction**: This decomposition is the structural
basis for **induction on Fin types**, just as `ℕ = {0} ∪ succ(ℕ)`
is the basis for induction on natural numbers. To prove a property
holds for all elements of `Fin (n+1)`, you can:
1. Handle `Fin.last n` as a base-like case
2. Handle `j.castSucc` by reducing to `Fin n` (the inductive step)

You've already proved every ingredient for showing
`|Fin n| = n` by induction: `|Fin 0| = 0` (Fin 0 is empty,
MeetFin L13), the decomposition `Fin (n+1) = Fin n ⊔ {last}`
(disjointly), and injectivity of castSucc (Level 8). The
formal proof will appear in the Cardinality world — but the
mathematical content is already in your hands.

There are actually *two* decompositions — the **castSucc/last**
decomposition you just proved, and the **0/succ** decomposition
from Level 10 (every element is either `0` or `j.succ`). Both
are structural tools for `Fin`. When you build tuples in the
next world: `vecSnoc` (adding at the back) uses the castSucc/last
decomposition, while `Fin.cons` (adding at the front) uses the
0/succ decomposition.

**Succ Injectivity** (Part 2): The value reasoning pattern —
convert to values, simplify, omega — handles injectivity
automatically. This property — equal outputs imply equal inputs —
is called **injectivity**. In Lean, `Function.Injective f` means
`forall a b, f a = f b -> a = b`. You just proved
`Function.Injective Fin.castSucc` (in Level 8) and
`Function.Injective Fin.succ` (in Level 9). You'll use injectivity
formally in the FinsetImage world.

Here's your navigation toolkit:

| Tool | What it does | Val lemma |
|---|---|---|
| `Fin.last n` | Maximum element of `Fin (n+1)` | `Fin.val_last` |
| `i.castSucc` | Embed into larger type (same value) | `Fin.val_castSucc` |
| `i.succ` | Move forward by 1 | `Fin.val_succ` |

And the proof recipes:

| Recipe | Pattern |
|---|---|
| Compare `Fin` values | val lemmas + `omega` |
| Prove `Fin` equality | `ext` + val lemmas |
| Prove `Fin` inequality | `ext_iff at h` + val lemmas at `h` + `omega` |
| Prove injectivity | `ext_iff at h` + val lemmas at `h` + `ext` + `omega` or `exact h` |
| Identify as `last` | `ext; rw [Fin.val_last]` |
| Find `castSucc` preimage | `use ⟨i.val, h⟩; ext; rw [Fin.val_castSucc]` |

**Where this is going**: In the next world (FinTuples), you'll use
`Fin n → α` to model tuples — ordered lists of fixed length.
The `0`/`succ` decomposition powers `Fin.cons` (adding at the front),
and the `castSucc`/`last` decomposition powers `vecSnoc` (adding at
the back).
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem Fin.succ_inj Fin.castSucc_inj Fin.forall_fin_two Fin.lastCases Fin.reverseInduction Fin.eq_zero_or_eq_succ Fin.cases
