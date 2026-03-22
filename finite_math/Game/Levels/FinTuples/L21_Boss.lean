import Game.Metadata

World "FinTuples"
Level 21

Title "Boss: Two Strategies, Two Tuples"

Introduction "
# Boss: Proving Tuples Are Equal

This boss has two parts, testing both reconstruction strategies.

**Part 1 — Front reconstruction**: You're given tuples `f` and `g`
described in different ways:
- `f` by its head and tail: `hf0 : f 0 = 1`, `hft : Fin.tail f = ![2, 3]`
- `g` pointwise: `hg : forall i, g i = i.val + 1`

Use the **cons reconstruction** from Level 20 to determine `f`,
then `ext` + case split to verify `f = g`.

**Part 2 — Back reconstruction**: You're given a tuple `p`
described by its init and last element:
- `hpi : Fin.init p = ![10, 20]`
- `hpl : p (Fin.last 2) = 30`

Use the **snoc reconstruction** (`vecSnoc_self_init` + `.symm`)
to determine `p = vecSnoc ![10, 20] 30`.

This boss combines:
- `Fin.cons_self_tail` + `.symm` + `rw ... at` (front reconstruction)
- `vecSnoc_self_init` + `.symm` + `rw ... at` (back reconstruction)
- `ext` + nested `cases` (pointwise verification)
- `rw` with a universally quantified hypothesis
"

/-- Two tuples reconstructed from different ends. -/
Statement (f g : Fin 3 → ℕ)
    (hf0 : f 0 = 1) (hft : Fin.tail f = ![2, 3])
    (hg : ∀ i : Fin 3, g i = i.val + 1)
    (p : Fin 3 → ℕ)
    (hpi : Fin.init p = ![10, 20])
    (hpl : p (Fin.last 2) = 30) :
    f = g ∧ p = vecSnoc ![10, 20] 30 := by
  Hint "The goal is a conjunction. Use `constructor` to split
  into Part 1 and Part 2."
  constructor
  -- Part 1: front reconstruction + pointwise verification
  · Hint "Part 1: determine `f` using cons reconstruction.
    `have hf : f = ![1, 2, 3] := by`
    then inside: `have key := (Fin.cons_self_tail f).symm`
    followed by `rw [hf0, hft] at key` and `exact key`."
    have hf : f = ![1, 2, 3] := by
      have key := (Fin.cons_self_tail f).symm
      rw [hf0, hft] at key
      exact key
    Hint "Good! Now use `ext ⟨v, hv⟩` to reduce `f = g` to
    checking each index."
    ext ⟨v, hv⟩
    Hint "Rewrite `f` using `hf` and `g` using `hg`:
    `rw [hf, hg]`."
    rw [hf, hg]
    Hint "Now case-split on `v` to verify each index."
    Hint (hidden := true) "`cases v with | zero | succ n`"
    cases v with
    | zero =>
      Hint (hidden := true) "Both sides evaluate to 1. Use `rfl`."
      rfl
    | succ n =>
      Hint (hidden := true) "Continue: `cases n with | zero | succ m`"
      cases n with
      | zero => rfl
      | succ m =>
        Hint (hidden := true) "`cases m with | zero | succ k`"
        cases m with
        | zero => rfl
        | succ k => exact absurd hv (by omega)
  -- Part 2: back reconstruction
  · Hint "Part 2: determine `p` using snoc reconstruction.
    Use `have key := (vecSnoc_self_init p).symm`."
    have key := (vecSnoc_self_init p).symm
    Hint "Now substitute the known last element and init:
    `rw [hpl, hpi] at key`."
    rw [hpl, hpi] at key
    Hint "Now `key` matches the goal. Use `exact key`."
    exact key

Conclusion "
Congratulations — you've completed **Fin Tuples**!

Here's your tuple toolkit:

| Tool | What it does | Learned in |
|---|---|---|
| `![a, b, c]` | Build tuple with vec notation | Levels 1-2 |
| `use` + `constructor` | Construct and verify a tuple | Level 3 |
| `Fin.cons a f` | Prepend element to tuple | Level 4 |
| `Fin.cons_val_zero` | `Fin.cons a f 0 = a` | Level 5 |
| `Fin.cons_val_succ` | `Fin.cons a f i.succ = f i` | Level 5 |
| `Fin.tail f` | Drop the first element | Level 6 |
| `Fin.cons_self_tail f` | `cons (f 0) (tail f) = f` | Level 7 |
| Round-trip | `tail (cons a g) = g` and `(cons a g) 0 = a` | Level 8 |
| `vecSnoc f x` | Append element to tuple | Level 9 |
| `vecSnoc_last` / `vecSnoc_castSucc` | Access snoc'd elements | Level 9 |
| `Fin.init f` | Drop the last element | Level 10 |
| `vecSnoc_self_init f` | `vecSnoc (init f) (f (last n)) = f` | Level 11 |
| `ext i` | Reduce function equality to pointwise | Level 12 |
| Tuple composition | `g circ f` transforms tuples | Level 13 |
| Tuples as data | Verify concrete computations on tuples | Level 14 |
| Cons injectivity | Equal cons'd tuples have equal parts | Level 15 |
| Snoc injectivity | Equal snoc'd tuples have equal parts | Level 16 |
| `Fin.elim0 i` | Eliminate impossible `Fin 0` | Level 17 |
| `ext` + case split | Prove `f = ![...]` by index | Level 18 |
| `.symm` | Flip an equation | Level 19 |
| Reconstruction | `.symm` + `rw at` from head/tail or init/last | Level 20 |

**Proof strategies**:
- **Index-by-index** (`ext` + `cases`): when you know each value
- **Front reconstruction** (`cons_self_tail.symm` + `rw`): when you know head + tail
- **Back reconstruction** (`vecSnoc_self_init.symm` + `rw`): when you know init + last

**The big picture**: `Fin n -> alpha` models ordered tuples. `Fin.cons` builds
from the front, `vecSnoc` from the back. Both have decomposition (tail/init)
and reconstruction (cons_self_tail/vecSnoc_self_init) identities. Function
extensionality (`ext`) lets you prove two tuples are equal index by index.
The round-trip identities (cons then tail gives back the same tuple, and
vice versa) mean that `Fin.cons` and `(head, tail)` form a **bijection**
between `alpha x (Fin n -> alpha)` and `Fin (n+1) -> alpha`. In later
worlds, you'll formalize this idea as an `Equiv` (equivalence).

**Where this is going**: Tuples are the building blocks for **big operators**
like $\\sum_{i=0}^{n-1} f(i)$, written `\\sum i, f i` in Lean. Summing the
entries of a tuple `f : Fin n \\to \\mathbb{N}` is exactly what big operators
do — and that's where this course is headed after Finset.

Next up: the Pset (problem set) world, which will test these skills
on fresh problems without scaffolding.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
