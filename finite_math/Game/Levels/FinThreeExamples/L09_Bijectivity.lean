import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 9

Title "A bijection on Fin 3"

Introduction
"
# Proving Bijectivity on `Fin 3`

A function is **bijective** if it is both injective and surjective.
In Lean, `Function.Bijective f` is defined as
`Function.Injective f ∧ Function.Surjective f`.

## The function

You have already proved (in Levels 4 and 5) that the cyclic shift
`0 ↦ 1, 1 ↦ 2, 2 ↦ 0` on `Fin 3` is both injective and surjective.
Now put these together to prove it is bijective.

You will re-prove both properties for the same function. This is
deliberate practice: the point is to combine two familiar proof
moves (`fin_cases` + contradiction closer for injectivity, `fin_cases`
+ preimage witness for surjectivity) into a single structured proof
using `constructor`.

Proving injectivity and surjectivity as separate named lemmas and
then combining them is standard Lean practice, not just a game
exercise. Breaking complex goals into smaller named pieces is how
most real Lean proofs are organized.

## Your task

Prove `Function.Bijective f` for the cyclic shift.

Since `Function.Bijective` is a conjunction, start with `constructor`
to split into two goals: injectivity and surjectivity.

For the injectivity goal, use the proof pattern from Level 4:
`intro a b h; fin_cases a <;> fin_cases b <;> closer`.

For the surjectivity goal, use the proof pattern from Level 5:
`intro b; fin_cases b` and then `exact ⟨witness, rfl⟩` in each case.

This level is about **integration**: combining two previously
practiced proof moves into a single structured proof.
"

/-- The cyclic shift on `Fin 3` is bijective. -/
Statement : Function.Bijective
    (fun i : Fin 3 => match i with | 0 => (1 : Fin 3) | 1 => 2 | 2 => 0) := by
  Hint "Since `Function.Bijective f` is `Injective f ∧ Surjective f`,
  start with `constructor` to split into two subgoals."
  constructor
  · Hint "First goal: injectivity. Use the exhaustive proof from Level 4.
    Try `intro a b h`."
    intro a b h
    Hint "Now enumerate all pairs: `fin_cases a <;> fin_cases b` and close
    each case."
    Hint (hidden := true) "`fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)`"
    fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)
  · Hint "Second goal: surjectivity. Use the preimage-finding proof from Level 5.
    Try `intro b`."
    intro b
    Hint "Split into cases for each codomain element: `fin_cases b`."
    fin_cases b
    · Hint "Find the preimage of `0`. The cyclic shift sends `2 ↦ 0`. Try `exact ⟨2, rfl⟩`."
      exact ⟨2, rfl⟩
    · Hint "Find the preimage of `1`. The cyclic shift sends `0 ↦ 1`. Try `exact ⟨0, rfl⟩`."
      exact ⟨0, rfl⟩
    · Hint "Find the preimage of `2`. The cyclic shift sends `1 ↦ 2`. Try `exact ⟨1, rfl⟩`."
      exact ⟨1, rfl⟩

/-- `Function.Bijective f` means `Function.Injective f ∧ Function.Surjective f`.
A function is bijective if it is both injective (one-to-one) and surjective (onto).

A bijection between finite sets of the same size is a **permutation**.

**In Lean**: Use `constructor` to split into the injective and surjective parts.

**Example**: The identity function is bijective. The cyclic shift `0 ↦ 1 ↦ 2 ↦ 0`
on `Fin 3` is bijective (it is a permutation). -/
DefinitionDoc Function.Bijective as "Function.Bijective"

NewDefinition Function.Bijective

DisabledTactic trivial decide native_decide simp aesop simp_all norm_num

Conclusion
"
The cyclic shift `0 ↦ 1, 1 ↦ 2, 2 ↦ 0` on `Fin 3` is bijective --- it is a
one-to-one correspondence from `{0, 1, 2}` to itself.

The proof combined two independent subproofs:
- **Injectivity** (Level 4 pattern): checked all 9 pairs, confirmed no collisions
- **Surjectivity** (Level 5 pattern): found a preimage for each codomain element

A bijection from a finite set to itself is a **permutation**. The cyclic
shift is one of the 6 permutations of `Fin 3` (since $3! = 6$). In a later
world, you will study `Equiv.Perm (Fin 3)` and work with all 6 of them.

**Integration skill**: This level required no new proof moves --- only
combining previously practiced moves (`constructor`, `fin_cases`,
`congr_arg`, `norm_num`, `exact ⟨_, rfl⟩`) into a single structured proof.

**In plain language**: \"The function $f$ with $f(0)=1$, $f(1)=2$, $f(2)=0$
is a bijection from $\\{0, 1, 2\\}$ to itself. It is injective because
its outputs are all distinct, and surjective because every element
appears as an output.\"
"
