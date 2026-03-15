import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 11

Title "Boss: The swap permutation on Fin 3"

Introduction
"
# Boss Level: A Complete Function Analysis

Time to integrate everything from this world.

Consider the function `f : Fin 3 → Fin 3` defined by:
- `f 0 = 0`
- `f 1 = 2`
- `f 2 = 1`

This is the \"swap 1 and 2\" permutation. It fixes `0` and exchanges
`1` with `2`. Mathematically, it is multiplication by 2 modulo 3:
- `2 * 0 = 0`
- `2 * 1 = 2`
- `2 * 2 = 4 ≡ 1 (mod 3)`

The outputs are `0, 2, 1` --- all distinct. So `f` is a bijection.

## Your task

Prove that this function is **bijective**.

You already know that `Function.Bijective f` means
`Function.Injective f ∧ Function.Surjective f` (from Level 9).
Use `constructor` to split the conjunction, then prove each part
using the patterns from Levels 4 and 5.

There is no new material --- only integration of skills from
Levels 1 through 9.
"

/-- The swap permutation on `Fin 3` is bijective. -/
Statement : Function.Bijective
    (fun i : Fin 3 => match i with | 0 => (0 : Fin 3) | 1 => 2 | 2 => 1) := by
  Hint "The goal is a conjunction: injectivity ∧ surjectivity. Use `constructor`
  to split into two subgoals."
  constructor
  · Hint "Prove injectivity. Use the pattern from Level 4:
    `intro a b h; fin_cases a <;> fin_cases b <;> closer`."
    Hint (hidden := true) "Full closer:
    `first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)`"
    intro a b h
    fin_cases a <;> fin_cases b <;>
      first | rfl | (exfalso; have := congr_arg Fin.val h; norm_num at this)
  · Hint "Prove surjectivity. Use the pattern from Level 5:
    `intro b; fin_cases b` then provide preimages."
    Hint (hidden := true) "The preimages: `0 = f 0`, `1 = f 2`, `2 = f 1`.
    After `fin_cases b`, use `exact ⟨0, rfl⟩`, `exact ⟨2, rfl⟩`, `exact ⟨1, rfl⟩`."
    intro b
    fin_cases b
    · Hint "Find the preimage of `0`. Since `f 0 = 0`, try `exact ⟨0, rfl⟩`."
      exact ⟨0, rfl⟩
    · Hint "Find the preimage of `1`. Since `f 2 = 1`, try `exact ⟨2, rfl⟩`."
      exact ⟨2, rfl⟩
    · Hint "Find the preimage of `2`. Since `f 1 = 2`, try `exact ⟨1, rfl⟩`."
      exact ⟨1, rfl⟩

DisabledTactic trivial decide native_decide simp aesop simp_all omega norm_num

Conclusion
"
Congratulations on completing the World of `Fin 3`!

You proved that the swap function `0 ↦ 0, 1 ↦ 2, 2 ↦ 1` on `Fin 3` is
bijective --- a one-to-one correspondence from `{0, 1, 2}` to itself,
and therefore a permutation.

| Input | Output | Note |
|-------|--------|------|
|   0   |   0    | Fixed point |
|   1   |   2    | $2 \\cdot 1 = 2$ |
|   2   |   1    | $2 \\cdot 2 = 4 \\equiv 1 \\pmod{3}$ |

The boss required combining:
- `constructor` to split the conjunction
- `intro a b h; fin_cases a <;> fin_cases b` for injectivity
- `congr_arg Fin.val h; norm_num at this` for contradictions
- `intro b; fin_cases b; exact ⟨_, rfl⟩` for surjectivity

## The six permutations of `Fin 3`

You have now worked with two of the six permutations of `{0, 1, 2}`:

| Permutation | Description | Type |
|------------|-------------|------|
| `0 ↦ 0, 1 ↦ 1, 2 ↦ 2` | Identity | Order 1 |
| `0 ↦ 1, 1 ↦ 2, 2 ↦ 0` | Cyclic shift (L04, L05, L09) | Order 3 |
| `0 ↦ 2, 1 ↦ 0, 2 ↦ 1` | Reverse cyclic shift | Order 3 |
| `0 ↦ 0, 1 ↦ 2, 2 ↦ 1` | Swap 1↔2 (L10, L11) | Order 2 |
| `0 ↦ 1, 1 ↦ 0, 2 ↦ 2` | Swap 0↔1 | Order 2 |
| `0 ↦ 2, 1 ↦ 1, 2 ↦ 0` | Swap 0↔2 | Order 2 |

There are exactly $3! = 6$ permutations because each is determined by
choosing where to send $0$ (3 options), then $1$ (2 options), then $2$
(1 option). In a later world, you will study `Equiv.Perm (Fin 3)` and
work with all six.

## What you learned in this world

| Skill | Level | Pattern |
|-------|-------|---------|
| Exhaustive enumeration | L01 | `fin_cases i` → `left`/`right` |
| Function verification | L02 | `fin_cases i` → per-case `norm_num` |
| Pair construction | L03 | `refine ⟨pair, ?_⟩` with constrained property |
| Injectivity proof | L04 | `intro a b h; fin_cases a <;> fin_cases b <;> closer` |
| Surjectivity proof | L05 | `intro b; fin_cases b` → per-case `exact ⟨_, rfl⟩` |
| Surjectivity failure | L06 | `intro h; obtain ⟨a, ha⟩ := h target; fin_cases a` |
| Injectivity failure | L07 | `intro h; have := h rfl; Fin.val extraction` |
| Cardinality counting | L08 | `rw [Fintype.card_prod, Fintype.card_fin]` |
| Bijectivity = inj + surj | L09 | `constructor` → prove each part |
| Involution verification | L10 | `fin_cases i <;> rfl` |
| Boss integration | L11 | All of the above in one proof |

## The key transfer insight

Every proof in this world has a short informal counterpart:

- \"$\\{0,1,2\\}$ consists of exactly $0$, $1$, and $2$.\" (L01)
- \"$2i + 1$ is odd for $i \\in \\{0,1,2\\}$: check $1, 3, 5$.\" (L02)
- \"$(0, 1)$ has distinct components because $0 \\neq 1$.\" (L03)
- \"$0 \\mapsto 1, 1 \\mapsto 2, 2 \\mapsto 0$ is injective: outputs are distinct.\" (L04)
- \"Same function is surjective: $0 = f(2)$, $1 = f(0)$, $2 = f(1)$.\" (L05)
- \"$\\{0,1,2\\} \\hookrightarrow \\{0,1,2,3\\}$ is not surjective: $3$ has no preimage.\" (L06)
- \"$0 \\mapsto 0, 1 \\mapsto 1, 2 \\mapsto 2, 3 \\mapsto 0$ is not injective: $f(0) = f(3)$.\" (L07)
- \"$\\{0,1,2\\} \\times \\{0,1,2\\}$ has $3 \\times 3 = 9$ elements.\" (L08)
- \"$0 \\mapsto 1 \\mapsto 2 \\mapsto 0$ is bijective (a permutation).\" (L09)
- \"Swapping 1 and 2 twice returns to the original arrangement.\" (L10)
- \"$0 \\mapsto 0, 1 \\mapsto 2, 2 \\mapsto 1$ is bijective (a permutation).\" (L11)

The Lean proofs made all of these precise, but the mathematical content
is elementary. That is the point of an example world: to make abstract
definitions tangible by grounding them in specific, small cases.

You are now ready to move on to richer finite collections: multisets
and finsets.
"
