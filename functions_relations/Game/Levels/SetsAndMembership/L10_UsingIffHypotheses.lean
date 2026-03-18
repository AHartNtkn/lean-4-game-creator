import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 10

Title "Using Iff Hypotheses"

Introduction
"
In the last level you proved an iff. Now you will *use* one.

If you have `h : P ↔ Q`, you can extract its two directions:
- `h.mp` is the forward direction: `P → Q`
- `h.mpr` is the backward direction: `Q → P`

The names come from 'modus ponens' (mp) and 'modus ponens reverse' (mpr).

In this level, you have `h : ∀ n, P n ↔ Q n` — an iff that depends
on a variable. To use it at a specific value like `42`, first
specialize: `h 42` gives you `P 42 ↔ Q 42`. Then extract the forward
direction: `(h 42).mp` gives you `P 42 → Q 42`.

Combining these: `(h 42).mp hp` takes `hp : P 42` and produces `Q 42`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement (P Q : ℕ → Prop) (h : ∀ n, P n ↔ Q n) (hp : P 42) : Q 42 := by
  Hint "You have `h : ∀ n, P n ↔ Q n` and `hp : P 42`. To get `Q 42`,
  you need the forward direction of `h` at `n = 42`.

  Try `have h42 := h 42` to specialize `h` to `42`."
  have h42 := h 42
  Hint "Now `h42 : P 42 ↔ Q 42`. Extract the forward direction with `.mp`:
  try `exact h42.mp hp`."
  exact h42.mp hp

Conclusion
"
You extracted the forward direction of an iff hypothesis using `.mp`.

**Iff usage recipe**:
- `h.mp` extracts `P → Q` from `h : P ↔ Q`
- `h.mpr` extracts `Q → P` from `h : P ↔ Q`
- `h.mp hp` directly applies the forward direction to `hp : P`

**With universally quantified iff**:
- If `h : ∀ n, P n ↔ Q n`, then `h 42` gives `P 42 ↔ Q 42`
- And `(h 42).mp hp` applies the forward direction at `n = 42`
- You can combine: `exact (h 42).mp hp` in one step

This `(h x).mp` / `(h x).mpr` idiom appears frequently when
working with set equality proofs.
"
