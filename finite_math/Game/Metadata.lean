import GameServer
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Dedup
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Group.Finsupp

/-- The binomial theorem for natural numbers, without Nat.cast coercion.

`add_pow` works over any `CommSemiring R` and inserts `↑(Nat.choose n m)`
via `Nat.cast`. When `R = ℕ` the cast is definitionally `id`, so `exact`
and `apply` see through it, but `rw` does not (it needs a syntactic match).

This wrapper states the theorem directly over `ℕ` so that `rw` and
`Finset.sum_congr` work without fighting `Nat.cast`. -/
theorem add_pow_nat (x y n : ℕ) :
    (x + y) ^ n =
      ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m :=
  add_pow x y n

/-! ## Documentation for disabled tactics and theorems

These docs are needed by the GameServer when tactics/theorems are disabled.
They are placed here so all level files can reference them.
-/

/-! ### NNG4-baseline tactics

These tactics are assumed known from the Natural Number Game or
equivalent. They are introduced in Level 1 so the game doesn't warn
about missing introductions.
-/

/-- `exact e` closes the goal if `e` has exactly the type of the goal.

## Syntax
```
exact expression
```

## When to use it
When you have a term (variable, function application, constructor)
whose type matches the goal exactly.
-/
TacticDoc exact

/-- `rw [h]` rewrites the goal using an equation or iff `h`.

## Syntax
```
rw [h]           -- rewrite the goal
rw [h] at hyp    -- rewrite a hypothesis
rw [← h]         -- rewrite right-to-left
rw [h1, h2, h3]  -- chain multiple rewrites
```

## When to use it
When you have an equation `h : a = b` or iff `h : P ↔ Q` and want
to replace `a` with `b` (or `P` with `Q`) in the goal or a hypothesis.
-/
TacticDoc rw

/-- `intro x` introduces a universally quantified variable or an
antecedent of an implication into the context.

## Syntax
```
intro x       -- introduce one variable
intro x y z   -- introduce multiple variables
intro h       -- introduce an implication hypothesis
```

## When to use it
When the goal is `∀ x, P x` or `P → Q`.
-/
TacticDoc intro

/-- `cases x with | constructor₁ => ... | constructor₂ => ...`
performs case analysis on `x`, creating one subgoal per constructor.

## Syntax
```
cases x with
| constructor₁ args => tactic₁
| constructor₂ args => tactic₂
```

## When to use it
When you want to consider all possible forms of a value (e.g., natural
numbers are `zero` or `succ n`, propositions with `∨` have `inl` and `inr`).
-/
TacticDoc cases

/-- `have h := expr` introduces a new hypothesis `h` with value `expr`.

## Syntax
```
have h := expr           -- Lean infers the type
have h : type := expr    -- explicit type annotation
have h : type := by ...  -- prove the hypothesis with tactics
```

## When to use it
When you need an intermediate fact that isn't directly in your context.
-/
TacticDoc «have»

/-- `use expr` provides a witness for an existential goal `∃ x, P x`.

## Syntax
```
use expr
```

## When to use it
When the goal is `∃ x, P x` and you know which `x` works.
After `use expr`, the goal becomes `P expr`.
-/
TacticDoc use

/-- `left` selects the left disjunct of a goal `P ∨ Q`.

## Syntax
```
left
```

## When to use it
When the goal is `P ∨ Q` and you want to prove `P`.
-/
TacticDoc left

/-- `right` selects the right disjunct of a goal `P ∨ Q`.

## Syntax
```
right
```

## When to use it
When the goal is `P ∨ Q` and you want to prove `Q`.
-/
TacticDoc right

/-- `rfl` closes a goal of the form `a = a` (reflexivity).

## Syntax
```
rfl
```

## When to use it
When both sides of an equality are definitionally equal.
-/
TacticDoc rfl

/-- `constructor` splits a goal with a single constructor (like `∧` or `↔`)
into its components.

## Syntax
```
constructor
```

## When to use it
When the goal is `P ∧ Q` (splits into `P` and `Q`) or `P ↔ Q`
(splits into `P → Q` and `Q → P`).
-/
TacticDoc constructor

/-- `apply e` closes or simplifies the goal when `e` is a function,
implication, or theorem whose conclusion matches the goal's type.

## Syntax
```
apply e
```

## When to use it
When the goal is the *conclusion* of some known fact `e`. After
`apply e`, the remaining goals are the *premises* of `e`.

## Example
```
-- h : P → Q, Goal: Q
apply h
-- remaining goal: P
```
-/
TacticDoc apply

/-- `norm_num` evaluates numerical expressions and closes arithmetic
goals that can be decided by computation.

## Syntax
```
norm_num
```

## When to use it
When the goal is a concrete numerical fact like `2 + 3 = 5` or `7 < 10`.

Disabled in levels where manual arithmetic reasoning is the lesson.
-/
TacticDoc norm_num

/-! ### Baseline disabled tactics

These tactics are disabled globally because they close goals that
the player should learn to handle manually.
-/

/-- `linarith` closes goals that are linear arithmetic consequences
of hypotheses. It handles inequalities and equalities over ordered
fields and rings.

Disabled in levels where manual inequality chaining is the lesson.
-/
TacticDoc linarith

/-- `nlinarith` extends `linarith` with nonlinear reasoning by
multiplying hypotheses together before applying linear arithmetic.

Disabled in levels where manual algebraic manipulation is the lesson.
-/
TacticDoc nlinarith

/-- `trivial` attempts to close the goal using a combination of
basic tactics (`rfl`, `exact True.intro`, `assumption`).

Disabled because it bypasses the learning of specific proof steps.
-/
TacticDoc trivial

/-- `decide` closes goals that are decidable propositions by
evaluating them computationally.

Disabled because it bypasses manual reasoning about finite types.
-/
TacticDoc «decide»

/-- `native_decide` is like `decide` but uses native code evaluation
for faster computation.

Disabled for the same reason as `decide`.
-/
TacticDoc native_decide

/-- `simp` applies a set of simplification lemmas to the goal
and hypotheses.

## `simp` vs `simp only`

- **`simp`** uses a large default lemma set — convenient but unpredictable
- **`simp only [lemma₁, lemma₂, ...]`** uses only the lemmas you specify

Prefer `simp only` when you want to control exactly which rewrites happen.
`simp only` replaces tedious chains of `rw` calls with a single targeted
simplification. For finset proofs, a common pattern:
```
simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
           Finset.mem_insert, Finset.mem_singleton]
```

Disabled in early levels to force manual rewriting and to ensure
the player understands each proof step.
-/
TacticDoc simp

/-- `aesop` is a general-purpose automation tactic that combines
multiple strategies to close goals.

Disabled to force manual proof construction.
-/
TacticDoc aesop

/-- `simp_all` applies `simp` to all hypotheses and the goal
simultaneously.

Disabled for the same reason as `simp`.
-/
TacticDoc simp_all

/-- `omega` solves linear arithmetic goals over `ℕ` and `ℤ`.
It handles equalities, inequalities, and disequalities involving
addition, subtraction, and multiplication by literals.

## Syntax
```
omega
```

## When to use it
When the goal is a concrete numeric fact like `5 ≠ 3`, `3 + 4 = 7`,
or `n < n + 1`.
-/
TacticDoc omega

/-- `by_cases h : P` splits the goal into two cases: one where `h : P`
holds and one where `h : ¬P` holds.

Disabled in levels where the taught destructuring + nested `cases`
pattern is the intended approach to case analysis.
-/
TacticDoc by_cases

/-- `tauto` closes goals that are propositional tautologies. It handles
`∨`, `∧`, `→`, `¬`, `↔`, `True`, `False`, and can use `rfl` for equalities.

Disabled in levels where the learner should construct proofs manually
using `left`/`right`, `constructor`, and specific lemmas.
-/
TacticDoc tauto

/-- `ring` closes goals that are equalities in commutative (semi)rings
by normalizing both sides.

Disabled in levels where the learner should use specific card_* lemmas
rather than letting ring close arithmetic goals directly.
-/
TacticDoc ring

/-- `ring_nf` is a normalization variant of `ring` that simplifies ring
expressions without necessarily closing the goal.

Disabled for the same reason as `ring`.
-/
TacticDoc ring_nf

/-! ### Fintype-specific disabled theorems -/

/-- `Nat.mul_comm` states that `a * b = b * a` for natural numbers.

Disabled in levels where the learner should use bijective counting
(`Equiv` + `card_congr`) rather than arithmetic commutativity.
-/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Fintype"

/-- `mul_comm` states that `a * b = b * a` in any commutative monoid.

Disabled in levels where the learner should use bijective counting
(`Equiv` + `card_congr`) rather than arithmetic commutativity.
-/
TheoremDoc mul_comm as "mul_comm" in "Fintype"

/-! ### MeetFin-specific disabled tactics and theorems -/

/-- `fin_cases` automatically performs case analysis on elements of
finite types like `Fin n`. It replaces a variable `x : Fin n` with
each possible value `0, 1, ..., n-1`.

Disabled in early levels to force manual case analysis.
-/
TacticDoc fin_cases

/-- `interval_cases` performs case analysis on a natural number or
integer variable whose value is bounded by hypotheses.

Disabled in early levels to force manual case analysis.
-/
TacticDoc interval_cases

/-- `Fin.forall_fin_two` states that a predicate holds for all
elements of `Fin 2` if and only if it holds for `0` and `1`.
-/
TheoremDoc Fin.forall_fin_two as "Fin.forall_fin_two" in "Fin"

/-- `Unique.eq_default` states that in a type with exactly one element,
every element equals the default.
-/
TheoremDoc Unique.eq_default as "Unique.eq_default" in "Fin"

/-- `Subsingleton.elim` states that in a type with at most one element,
any two elements are equal.
-/
TheoremDoc Subsingleton.elim as "Subsingleton.elim" in "Fin"

/-! ### FinNavigation-specific disabled theorems -/

/-- `Fin.castSucc_lt_last` states that `i.castSucc < Fin.last n` for
any `i : Fin n`. This follows because `i.castSucc.val = i.val < n = (Fin.last n).val`.
-/
TheoremDoc Fin.castSucc_lt_last as "Fin.castSucc_lt_last" in "Fin"

/-- `Fin.castSucc_ne_last` states that `i.castSucc ≠ Fin.last n` for
any `i : Fin n`.
-/
TheoremDoc Fin.castSucc_ne_last as "Fin.castSucc_ne_last" in "Fin"

/-- `Fin.castSucc_lt_succ` states that `i.castSucc < i.succ` for
any `i : Fin n`. This follows from the value-level fact
`i.val < i.val + 1`.
-/
TheoremDoc Fin.castSucc_lt_succ as "Fin.castSucc_lt_succ" in "Fin"

/-- `Fin.succ_pos` states that `0 < a.succ` for any `a : Fin n`.
This follows from the value-level fact `0 < a.val + 1`.
-/
TheoremDoc Fin.succ_pos as "Fin.succ_pos" in "Fin"

/-- `Fin.succ_ne_zero` states that `a.succ ≠ 0` for any `a : Fin n`.
This is the `≠` version of `Fin.succ_pos`: since `a.succ.val ≥ 1 > 0`,
a successor can never equal zero.
-/
TheoremDoc Fin.succ_ne_zero as "Fin.succ_ne_zero" in "Fin"

/-- `Fin.succ_inj` states that `a.succ = b.succ ↔ a = b` for
elements of `Fin n`. In other words, `Fin.succ` is injective.
-/
TheoremDoc Fin.succ_inj as "Fin.succ_inj" in "Fin"

/-- `Fin.castSucc_inj` states that `a.castSucc = b.castSucc ↔ a = b`
for elements of `Fin n`. In other words, `Fin.castSucc` is injective.
-/
TheoremDoc Fin.castSucc_inj as "Fin.castSucc_inj" in "Fin"

/-- `Fin.le_last i` states that `i ≤ Fin.last n` for any `i : Fin (n + 1)`.
Every element is at most the last element.
-/
TheoremDoc Fin.le_last as "Fin.le_last" in "Fin"

/-- `Fin.lastCases` is an elimination principle for `Fin (n + 1)`: given
a value for `Fin.last n` and a function on `castSucc` images, produce
a value for any element.
-/
TheoremDoc Fin.lastCases as "Fin.lastCases" in "Fin"

/-- `Fin.reverseInduction` is an induction principle for `Fin (n + 1)`
that starts from `Fin.last n` and works downward.
-/
TheoremDoc Fin.reverseInduction as "Fin.reverseInduction" in "Fin"

/-- `Fin.cases` is an elimination principle for `Fin (n + 1)`: given
a value for `0` and a function on `succ` images, produce a value for
any element.
-/
TheoremDoc Fin.cases as "Fin.cases" in "Fin"

/-- `Fin.eq_zero_or_eq_succ i` states that every `i : Fin (n + 1)`
is either `0` or `j.succ` for some `j : Fin n`.
-/
TheoremDoc Fin.eq_zero_or_eq_succ as "Fin.eq_zero_or_eq_succ" in "Fin"

/-! ### FinsetBasics-specific disabled theorems -/

/-- `Finset.mem_insert_self a s` proves `a ∈ insert a s` directly.

Disabled in levels where the learner should prove membership by
rewriting with `Finset.mem_insert` and choosing `left`/`right`.
-/
TheoremDoc Finset.mem_insert_self as "Finset.mem_insert_self" in "Finset"

/-- `Finset.mem_insert_of_mem h` proves `a ∈ insert b s` from `h : a ∈ s`.

Disabled in levels where the learner should prove membership by
rewriting with `Finset.mem_insert` and peeling inserts manually.
-/
TheoremDoc Finset.mem_insert_of_mem as "Finset.mem_insert_of_mem" in "Finset"

/-- `Finset.insert_nonempty a s` proves `(insert a s).Nonempty` directly.

Disabled in levels where the learner should prove Nonempty by
providing a witness with `use` and proving membership.
-/
TheoremDoc Finset.insert_nonempty as "Finset.insert_nonempty" in "Finset"

/-- `Finset.singleton_nonempty a` proves `({a}).Nonempty` directly.

Disabled in levels where the learner should prove Nonempty by
providing a witness with `use` and proving membership.
-/
TheoremDoc Finset.singleton_nonempty as "Finset.singleton_nonempty" in "Finset"

/-- `Finset.not_mem_range_self` proves `n ∉ Finset.range n` directly.

Disabled in levels where the learner should prove non-membership
by assuming membership, rewriting with `mem_range`, and deriving
a contradiction with `omega`.
-/
TheoremDoc Finset.not_mem_range_self as "Finset.not_mem_range_self" in "Finset"

/-! ### FinTuples-specific definitions and theorems -/

/-- Non-dependent version of `Fin.cons_zero`.
`Fin.cons a f 0 = a` — accessing the head of a cons'd tuple returns the prepended element. -/
theorem Fin.cons_val_zero {n : ℕ} {α : Type*} (a : α) (f : Fin n → α) :
    (Fin.cons a f : Fin (n+1) → α) 0 = a := rfl

/-- Non-dependent version of `Fin.cons_succ`.
`Fin.cons a f i.succ = f i` — accessing later elements of a cons'd tuple returns the tail. -/
theorem Fin.cons_val_succ {n : ℕ} {α : Type*} (a : α) (f : Fin n → α) (i : Fin n) :
    (Fin.cons a f : Fin (n+1) → α) i.succ = f i := rfl

/-- `vecSnoc f x` appends element `x` to the end of tuple `f`,
producing a tuple of length `n + 1`.

This is the non-dependent wrapper around `Fin.snoc` for use with
concrete types like `Fin n → ℕ`.

## Type
`vecSnoc : (Fin n → α) → α → Fin (n + 1) → α`

## Element access
- `vecSnoc f x (Fin.last n) = x` (the appended element)
- `vecSnoc f x i.castSucc = f i` (the original tuple)

## Example
`vecSnoc ![10, 20] 30 = ![10, 20, 30]`
-/
def vecSnoc {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) : Fin (n + 1) → α :=
  @Fin.snoc n (fun _ => α) f x

/-- Accessing the last element of a snoc'd tuple gives back the appended element. -/
theorem vecSnoc_last {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) :
    vecSnoc f x (Fin.last n) = x :=
  @Fin.snoc_last n (fun _ => α) x f

/-- Accessing an earlier element of a snoc'd tuple gives the original tuple's value. -/
theorem vecSnoc_castSucc {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) (i : Fin n) :
    vecSnoc f x i.castSucc = f i :=
  @Fin.snoc_castSucc n (fun _ => α) x f i

/-- Appending the last element to the init recovers the original tuple. -/
theorem vecSnoc_self_init {n : ℕ} {α : Type*} (f : Fin (n + 1) → α) :
    vecSnoc (Fin.init f) (f (Fin.last n)) = f :=
  Fin.snoc_init_self f

/-- `vecSnoc_self_init f` states that
`vecSnoc (Fin.init f) (f (Fin.last n)) = f`.

Every tuple equals its init snoc'd with its last element.

## Syntax
```
exact vecSnoc_self_init f  -- proves vecSnoc (init f) (f (last n)) = f
```

## When to use it
When you need to decompose a tuple into its earlier elements
and its last element.
-/
TheoremDoc vecSnoc_self_init as "vecSnoc_self_init" in "Fin"

/-- `funext` is the function extensionality theorem: if two functions
agree on every input, they are equal.

Disabled in levels where the `ext` tactic should be used interactively.
-/
TheoremDoc funext as "funext" in "Fin"

/-- `congrFun h a` extracts pointwise agreement from a function equality.
If `h : f = g`, then `congrFun h a : f a = g a`.

## Syntax
```
have h0 := congrFun h 0     -- extract agreement at index 0
have hi := congrFun h i.succ -- extract agreement at index i.succ
```

## When to use it
When you have `h : f = g` and need to deduce that `f a = g a` at a
specific input `a`. This is the **pointwise extraction** move: turn
a global function equality into a local value equality.
-/
TheoremDoc congrFun as "congrFun" in "Fin"

/-- `Function.comp_apply` states that `(g ∘ f) x = g (f x)`.

## Syntax
```
rw [Function.comp_apply]  -- unfolds (g ∘ f) x to g (f x)
```

## When to use it
When you need to unfold a composition `(g ∘ f) x` to the explicit
application `g (f x)` — for example, before substituting formulas
for `f` and `g` with `rw`.
-/
TheoremDoc Function.comp_apply as "Function.comp_apply" in "Fin"

/-! ### BigOp-specific disabled theorems -/

/-- `Finset.sum_pair` evaluates a two-element sum directly.

Disabled to force the learner to use `sum_insert` + `sum_singleton`
peel pattern rather than a shortcut.
-/
TheoremDoc Finset.sum_pair as "Finset.sum_pair" in "BigOp"

/-- `Finset.prod_pair` evaluates a two-element product directly.

Disabled to force the learner to use `prod_insert` + `prod_singleton`
peel pattern rather than a shortcut.
-/
TheoremDoc Finset.prod_pair as "Finset.prod_pair" in "BigOp"

/-- `Finset.sum_eq_card_nsmul` states that if `∀ x ∈ s, f x = c`,
then `∑ x ∈ s, f x = s.card • c`.

Disabled in BigOpAlgebra to force the learner to combine
`sum_congr` + `sum_const` rather than using this shortcut.
-/
TheoremDoc Finset.sum_eq_card_nsmul as "Finset.sum_eq_card_nsmul" in "BigOp"

/-- `Finset.sum_nsmul` states that
`∑ x ∈ s, n • f x = n • ∑ x ∈ s, f x`.

Disabled defensively in BigOpAlgebra to prevent bypassing
`sum_add_distrib` via scalar factoring.
-/
TheoremDoc Finset.sum_nsmul as "Finset.sum_nsmul" in "BigOp"

/-- `Finset.sum_const` states that `∑ x ∈ s, c = s.card • c`.

Disabled in FinsetInduction to force manual induction proofs.
-/
TheoremDoc Finset.sum_const as "Finset.sum_const" in "BigOp"

/-- `Finset.card_eq_sum_ones` states that `s.card = ∑ x ∈ s, 1`.

Disabled in FinsetInduction to force manual induction proof of
the same identity.
-/
TheoremDoc Finset.card_eq_sum_ones as "Finset.card_eq_sum_ones" in "Finset"

/-- `Finset.sum_const_zero` states that `∑ x ∈ s, (0 : M) = 0`.

Disabled in FinsetInduction to force manual induction proof.
-/
TheoremDoc Finset.sum_const_zero as "Finset.sum_const_zero" in "BigOp"

/-- `Finset.sum_eq_zero` states that if `∀ x ∈ s, f x = 0` then
`∑ x ∈ s, f x = 0`.

Disabled in FinsetInduction to prevent bypassing induction proofs.
-/
TheoremDoc Finset.sum_eq_zero as "Finset.sum_eq_zero" in "BigOp"

/-- `Finset.mul_sum` states that `c * ∑ x ∈ s, f x = ∑ x ∈ s, c * f x`.

Disabled in FinsetInduction to prevent bypassing the peel-IH-ring
induction pattern by factoring before the induction step.
-/
TheoremDoc Finset.mul_sum as "Finset.mul_sum" in "BigOp"

/-- `Finset.sum_mul` states that `(∑ x ∈ s, f x) * c = ∑ x ∈ s, f x * c`.

Disabled in FinsetInduction to prevent bypassing induction via
algebraic rearrangement.
-/
TheoremDoc Finset.sum_mul as "Finset.sum_mul" in "BigOp"

/-- `Finset.sum_range_succ'` states that
`∑ i ∈ range (n + 1), f i = f 0 + ∑ i ∈ range n, f (i + 1)`.

Peels off the **first** term of a sum over `Finset.range`.
Compare with `sum_range_succ` which peels off the **last** term.

## When to use it
When you want to split off `f 0` from a sum over `range (n + 1)`.
Useful when the first term is zero or has special structure.
-/
TheoremDoc Finset.sum_range_succ' as "Finset.sum_range_succ'" in "BigOp"

/-- `MulZeroClass.zero_mul` states that `0 * a = 0`.

Basic arithmetic fact: multiplying zero by anything gives zero.
-/
TheoremDoc MulZeroClass.zero_mul as "MulZeroClass.zero_mul" in "Arith"

/-- `add_zero` states that `a + 0 = a`.

Basic arithmetic fact: adding zero changes nothing.
-/
TheoremDoc add_zero as "add_zero" in "Arith"

/-- `Finset.sum_sub_distrib` states that
`∑ x ∈ s, (f x - g x) = (∑ x ∈ s, f x) - (∑ x ∈ s, g x)`.

Disabled in FinsetInduction to prevent bypassing telescoping
induction proofs.
-/
TheoremDoc Finset.sum_sub_distrib as "Finset.sum_sub_distrib" in "BigOp"

/-! ### Lattice-alias disabled theorems

These are lattice-level aliases for Finset operations. Disabled to prevent
bypassing element-wise Finset proofs with lattice automation.
-/

/-- `sup_eq_left` states `a ⊔ b = a ↔ b ≤ a` in a semilattice.
For Finsets, this means `s ∪ t = s ↔ t ⊆ s`.

Disabled to force element-wise reasoning about union via `ext` and `mem_union`.
-/
TheoremDoc sup_eq_left as "sup_eq_left" in "Order"

/-- `inf_eq_left` states `a ⊓ b = a ↔ a ≤ b` in a semilattice.
For Finsets, this means `s ∩ t = s ↔ s ⊆ t`.

Disabled to force element-wise reasoning about intersection via `ext` and `mem_inter`.
-/
TheoremDoc inf_eq_left as "inf_eq_left" in "Order"

/-- `sup_eq_right` states `a ⊔ b = b ↔ a ≤ b` in a semilattice.
For Finsets, this means `s ∪ t = t ↔ s ⊆ t`.

Disabled to force element-wise reasoning about union via `ext` and `mem_union`.
-/
TheoremDoc sup_eq_right as "sup_eq_right" in "Order"

/-- `inf_eq_right` states `a ⊓ b = b ↔ b ≤ a` in a semilattice.
For Finsets, this means `s ∩ t = t ↔ t ⊆ s`.

Disabled to force element-wise reasoning about intersection via `ext` and `mem_inter`.
-/
TheoremDoc inf_eq_right as "inf_eq_right" in "Order"

/-! ### FinsetOperations-specific disabled theorems -/

/-- `Finset.union_comm s t` proves `s ∪ t = t ∪ s` directly.

Disabled to force the learner to prove union commutativity using `ext`.
-/
TheoremDoc Finset.union_comm as "Finset.union_comm" in "Finset"

/-- `Finset.inter_comm s t` proves `s ∩ t = t ∩ s` directly.

Disabled to force the learner to prove intersection commutativity using `ext`.
-/
TheoremDoc Finset.inter_comm as "Finset.inter_comm" in "Finset"

/-- `Finset.mem_union_left t h` proves `a ∈ s ∪ t` from `h : a ∈ s`.

Disabled to force the learner to use `rw [Finset.mem_union]` and `left`.
-/
TheoremDoc Finset.mem_union_left as "Finset.mem_union_left" in "Finset"

/-- `Finset.mem_union_right s h` proves `a ∈ s ∪ t` from `h : a ∈ t`.

Disabled to force the learner to use `rw [Finset.mem_union]` and `right`.
-/
TheoremDoc Finset.mem_union_right as "Finset.mem_union_right" in "Finset"

/-- `Finset.mem_inter_of_mem h₁ h₂` proves `a ∈ s ∩ t` from
`h₁ : a ∈ s` and `h₂ : a ∈ t`.

Disabled to force the learner to use `rw [Finset.mem_inter]` and `constructor`.
-/
TheoremDoc Finset.mem_inter_of_mem as "Finset.mem_inter_of_mem" in "Finset"

/-- `Finset.mem_of_mem_inter_left h` extracts `a ∈ s` from `h : a ∈ s ∩ t`.

Disabled to force the learner to rewrite with `mem_inter` and use `.1`.
-/
TheoremDoc Finset.mem_of_mem_inter_left as "Finset.mem_of_mem_inter_left" in "Finset"

/-- `Finset.mem_of_mem_inter_right h` extracts `a ∈ t` from `h : a ∈ s ∩ t`.

Disabled to force the learner to rewrite with `mem_inter` and use `.2`.
-/
TheoremDoc Finset.mem_of_mem_inter_right as "Finset.mem_of_mem_inter_right" in "Finset"

/-- `Finset.subset_union_left` proves `s ⊆ s ∪ t` directly.

Disabled to force the learner to prove subset manually using `subset_iff`.
-/
TheoremDoc Finset.subset_union_left as "Finset.subset_union_left" in "Finset"

/-- `Finset.subset_union_right` proves `t ⊆ s ∪ t` directly.

Disabled to force the learner to prove subset manually using `subset_iff`.
-/
TheoremDoc Finset.subset_union_right as "Finset.subset_union_right" in "Finset"

/-- `Finset.inter_subset_left` proves `s ∩ t ⊆ s` directly.

Disabled to force the learner to prove subset manually.
-/
TheoremDoc Finset.inter_subset_left as "Finset.inter_subset_left" in "Finset"

/-- `Finset.inter_subset_right` proves `s ∩ t ⊆ t` directly.

Disabled to force the learner to prove subset manually.
-/
TheoremDoc Finset.inter_subset_right as "Finset.inter_subset_right" in "Finset"

/-- `Finset.union_inter_distrib_right s t u` proves
`(s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u)` directly.

Disabled to force the learner to prove distributivity using `ext`.
-/
TheoremDoc Finset.union_inter_distrib_right as "Finset.union_inter_distrib_right" in "Finset"

/-- `Finset.union_inter_distrib_left s t u` proves
`s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)` directly.

Disabled to force the learner to prove distributivity using `ext`.
-/
TheoremDoc Finset.union_inter_distrib_left as "Finset.union_inter_distrib_left" in "Finset"

/-- `Finset.union_self s` proves `s ∪ s = s` directly.

Disabled to force manual proof.
-/
TheoremDoc Finset.union_self as "Finset.union_self" in "Finset"

/-- `sup_comm` proves `a ⊔ b = b ⊔ a` for any semilattice with sup.
For finsets, `⊔` is `∪`, so this is a lattice-level alias for
`Finset.union_comm`.

Disabled alongside `Finset.union_comm`.
-/
TheoremDoc sup_comm as "sup_comm" in "Finset"

/-- `inf_comm` proves `a ⊓ b = b ⊓ a` for any semilattice with inf.
For finsets, `⊓` is `∩`, so this is a lattice-level alias for
`Finset.inter_comm`.

Disabled alongside `Finset.inter_comm`.
-/
TheoremDoc inf_comm as "inf_comm" in "Finset"

/-- `Finset.mem_of_mem_filter` extracts `x ∈ s` from
`x ∈ s.filter p`.

Disabled to force the learner to use `rw [Finset.mem_filter]` and `.1`.
-/
TheoremDoc Finset.mem_of_mem_filter as "Finset.mem_of_mem_filter" in "Finset"

/-- `Finset.pair_comm a b` proves `{a, b} = {b, a}` directly.

Disabled to force the learner to prove set equality manually
(via mutual containment or `ext`).
-/
TheoremDoc Finset.pair_comm as "Finset.pair_comm" in "Finset"

/-! ### Lattice-level aliases for Finset operations

Finset operations (∪, ∩) are lattice operations (⊔, ⊓) under the hood.
Every Finset identity has a lattice-level alias that must also be disabled.
-/

/-- `inf_sup_right` proves `(a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)` in any
distributive lattice. For finsets, this is `(s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u)`.

Disabled as a lattice alias for `Finset.union_inter_distrib_right`.
-/
TheoremDoc inf_sup_right as "inf_sup_right" in "Finset"

/-- `inf_sup_left` proves `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)` in any
distributive lattice. For finsets, this is `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`.

Disabled as a lattice alias for `Finset.inter_union_distrib_left`.
-/
TheoremDoc inf_sup_left as "inf_sup_left" in "Finset"

/-- `sup_inf_right` proves `(a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)` in any
distributive lattice. For finsets, this is `(s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u)`.

Disabled as a lattice alias for dual distributivity.
-/
TheoremDoc sup_inf_right as "sup_inf_right" in "Finset"

/-- `sup_inf_left` proves `a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)` in any
distributive lattice. For finsets, this is `s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)`.

Disabled as a lattice alias for `Finset.union_inter_distrib_left`.
-/
TheoremDoc sup_inf_left as "sup_inf_left" in "Finset"

/-- `inf_idem` proves `a ⊓ a = a`. For finsets, `s ∩ s = s`.

Disabled to prevent shortcutting set identity proofs.
-/
TheoremDoc inf_idem as "inf_idem" in "Finset"

/-- `sup_idem` proves `a ⊔ a = a`. For finsets, `s ∪ s = s`.

Disabled to prevent shortcutting set identity proofs.
-/
TheoremDoc sup_idem as "sup_idem" in "Finset"

/-- `inf_assoc` proves `(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)`. For finsets, this is
intersection associativity.

Disabled to prevent shortcutting set identity proofs.
-/
TheoremDoc inf_assoc as "inf_assoc" in "Finset"

/-- `sup_assoc` proves `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`. For finsets, this is
union associativity.

Disabled to prevent shortcutting set identity proofs.
-/
TheoremDoc sup_assoc as "sup_assoc" in "Finset"

/-- `le_antisymm` proves `a ≤ b → b ≤ a → a = b` in any partial order.
For finsets, `≤` is `⊆`, so this is a lattice alias for `Finset.Subset.antisymm`.

Disabled to force the learner to use `ext` or `Subset.antisymm` explicitly.
-/
TheoremDoc le_antisymm as "le_antisymm" in "Finset"

/-- `sup_inf_self` proves `a ⊔ (a ⊓ b) = a` (absorption law).
For finsets, `s ∪ (s ∩ t) = s`.

Disabled to force manual proof using `ext`.
-/
TheoremDoc sup_inf_self as "sup_inf_self" in "Finset"

/-- `inf_sup_self` proves `a ⊓ (a ⊔ b) = a` (dual absorption law).
For finsets, `s ∩ (s ∪ t) = s`.

Disabled to force manual proof using `ext`.
-/
TheoremDoc inf_sup_self as "inf_sup_self" in "Finset"

/-- `Finset.union_inter_cancel_left` proves `s ∪ (s ∩ t) = s` directly.

Disabled to force manual proof using `ext`.
-/
TheoremDoc Finset.union_inter_cancel_left as "Finset.union_inter_cancel_left" in "Finset"

/-- `Finset.inter_union_cancel_left` proves `s ∩ (s ∪ t) = s` directly.

Disabled to force manual proof using `ext`.
-/
TheoremDoc Finset.inter_union_cancel_left as "Finset.inter_union_cancel_left" in "Finset"

/-- `sdiff_sup` proves `a \ (b ⊔ c) = (a \ b) ⊓ (a \ c)` in a generalized
Boolean algebra. For finsets, `s \ (t ∪ u) = (s \ t) ∩ (s \ u)`.

Disabled to force manual proof using `ext`.
-/
TheoremDoc sdiff_sup as "sdiff_sup" in "Finset"

/-- `Finset.sdiff_union_distrib` or similar — proves De Morgan's law
for finsets directly.

Disabled to force manual proof using `ext`.
-/
TheoremDoc Finset.sdiff_inter_distrib_left as "Finset.sdiff_inter_distrib_left" in "Finset"

/-- `Finset.inter_self s` proves `s ∩ s = s` directly.

Disabled to force manual proof.
-/
TheoremDoc Finset.inter_self as "Finset.inter_self" in "Finset"

/-! ### Propositional logic lemmas that bypass manual reasoning -/

/-- `and_comm` proves `a ∧ b ↔ b ∧ a`. Commutativity of conjunction.

Disabled to force manual conjunction swapping with `.1`/`.2` and `⟨⟩`.
-/
TheoremDoc and_comm as "and_comm" in "Logic"

/-- `or_comm` proves `a ∨ b ↔ b ∨ a`. Commutativity of disjunction.

Disabled to force manual disjunction swapping with `cases` and `left`/`right`.
-/
TheoremDoc or_comm as "or_comm" in "Logic"

/-- `or_and_right` proves `(a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c)`.
Distributivity of conjunction over disjunction (right).

Disabled to force manual proof of distributivity.
-/
TheoremDoc or_and_right as "or_and_right" in "Logic"

/-- `or_and_left` proves `a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)`.
Distributivity of conjunction over disjunction (left).

Disabled to force manual proof of distributivity.
-/
TheoremDoc or_and_left as "or_and_left" in "Logic"

/-- `and_or_right` proves `(a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c)`.
Distributivity of disjunction over conjunction (right).

Disabled to force manual proof.
-/
TheoremDoc and_or_right as "and_or_right" in "Logic"

/-- `and_or_left` proves `a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)`.
Distributivity of disjunction over conjunction (left).

Disabled to force manual proof.
-/
TheoremDoc and_or_left as "and_or_left" in "Logic"

/-- `not_or` proves `¬(a ∨ b) ↔ ¬a ∧ ¬b`.
De Morgan's law for propositions.

Disabled to force manual negation handling.
-/
TheoremDoc not_or as "not_or" in "Logic"

/-! ### Additional lattice-level aliases -/

/-- `inf_le_left` proves `a ⊓ b ≤ a`. For finsets, `s ∩ t ⊆ s`.

Disabled to force manual subset proofs using `subset_iff`.
-/
TheoremDoc inf_le_left as "inf_le_left" in "Finset"

/-- `inf_le_right` proves `a ⊓ b ≤ b`. For finsets, `s ∩ t ⊆ t`.

Disabled to force manual subset proofs using `subset_iff`.
-/
TheoremDoc inf_le_right as "inf_le_right" in "Finset"

/-- `le_sup_left` proves `a ≤ a ⊔ b`. For finsets, `s ⊆ s ∪ t`.

Disabled to force manual subset proofs using `subset_iff`.
-/
TheoremDoc le_sup_left as "le_sup_left" in "Finset"

/-- `le_sup_right` proves `b ≤ a ⊔ b`. For finsets, `t ⊆ s ∪ t`.

Disabled to force manual subset proofs using `subset_iff`.
-/
TheoremDoc le_sup_right as "le_sup_right" in "Finset"

/-- `sdiff_sdiff_right_self` proves `x \ (x \ y) = x ⊓ y` in a
generalized Boolean algebra. For finsets, `s \ (s \ t) = s ∩ t`.

Disabled to force manual proof using `ext` and `by_contra`.
-/
TheoremDoc sdiff_sdiff_right_self as "sdiff_sdiff_right_self" in "Finset"

/-- `Finset.union_empty` proves `s ∪ ∅ = s` directly.

Disabled to force manual proof using `ext`.
-/
TheoremDoc Finset.union_empty as "Finset.union_empty" in "Finset"

/-- `Finset.empty_union` proves `∅ ∪ s = s` directly.

Disabled to force manual proof using `ext`.
-/
TheoremDoc Finset.empty_union as "Finset.empty_union" in "Finset"

/-- `sup_bot_eq` proves `a ⊔ ⊥ = a`. For finsets, `s ∪ ∅ = s`.

Lattice alias for `Finset.union_empty`.
-/
TheoremDoc sup_bot_eq as "sup_bot_eq" in "Finset"

/-- `bot_sup_eq` proves `⊥ ⊔ a = a`. For finsets, `∅ ∪ s = s`.

Lattice alias for `Finset.empty_union`.
-/
TheoremDoc bot_sup_eq as "bot_sup_eq" in "Finset"

/-! ### FinsetImage-specific disabled theorems -/

/-- `Finset.image_const h b` proves that `s.image (fun _ => b) = {b}` when
`h : s.Nonempty`. A constant function maps any nonempty finset to a singleton.

Disabled to force the learner to prove constant-image results manually
using backward extraction and `ext`.
-/
TheoremDoc Finset.image_const as "Finset.image_const" in "Finset"

/-- `Finset.image_eq_empty` states that `s.image f = ∅ ↔ s = ∅`.
The image of a finset is empty if and only if the finset itself is empty.

Disabled to force manual reasoning about image membership.
-/
TheoremDoc Finset.image_eq_empty as "Finset.image_eq_empty" in "Finset"

/-- `Finset.image_inter_subset f s t` proves that
`(s ∩ t).image f ⊆ s.image f ∩ t.image f`.
The image of an intersection is contained in the intersection of images.

Disabled to force manual proof using backward extraction.
-/
TheoremDoc Finset.image_inter_subset as "Finset.image_inter_subset" in "Finset"

/-- `Finset.image_inter s t hf` proves that
`(s ∩ t).image f = s.image f ∩ t.image f` when `hf : Function.Injective f`.
Under injectivity, image distributes over intersection.

Disabled to force manual proof combining extraction and injectivity.
-/
TheoremDoc Finset.image_inter as "Finset.image_inter" in "Finset"

/-- `Finset.image_inter_of_injOn s t hf` proves that
`(s ∩ t).image f = s.image f ∩ t.image f` when `hf` is injectivity
restricted to `s ∪ t` (`Set.InjOn`).

Disabled alongside `Finset.image_inter`.
-/
TheoremDoc Finset.image_inter_of_injOn as "Finset.image_inter_of_injOn" in "Finset"

/-! ### show and change tactics -/

/-- `show P` replaces the current goal with `P`, provided `P` is
definitionally equal to the current goal. This is useful when the
goal displays in unfamiliar notation (like lattice `⊔`/`⊓`) and
you want to convert it to familiar notation (`∪`/`∩`).

## Syntax
```
show x ∈ s ∪ t   -- when goal shows x ∈ s ⊔ t
```

## When to use it
When the goal's notation is unfamiliar but you know what it
should look like. `show` converts to any definitionally equal form.
-/
TacticDoc «show»

/-- `change P at h` replaces hypothesis `h` with `P`, provided `P` is
definitionally equal to the type of `h`. This is useful when a
hypothesis displays in unfamiliar notation (like lattice `⊓`) and
you want to convert it to familiar notation (`∩`).

## Syntax
```
change x ∈ s ∩ t at h   -- when h shows x ∈ s ⊓ t
```

## When to use it
When a hypothesis uses lattice notation (`⊔`, `⊓`, `≤`) and you
want to convert it to finset notation (`∪`, `∩`, `⊆`).
-/
TacticDoc «change»

/-! ### push_neg tactic -/

/-- `push_neg` pushes negations inward through quantifiers and connectives.
For example, `¬∀ x, P x` becomes `∃ x, ¬P x`.

Disabled in levels where `by_contra` is the intended technique.
-/
TacticDoc push_neg

/-! ### FinsetImage-specific disabled theorems -/

/-- `Finset.mem_image_of_mem f h` proves `f a ∈ s.image f` from `h : a ∈ s`.

Disabled to force the learner to use `rw [Finset.mem_image]` and provide
a witness manually with `use`.
-/
TheoremDoc Finset.mem_image_of_mem as "Finset.mem_image_of_mem" in "Finset"

/-- `Finset.image_subset_image h` proves `s₁.image f ⊆ s₂.image f`
from `h : s₁ ⊆ s₂`.

Disabled to force the learner to prove image monotonicity manually
by extracting and re-using witnesses.
-/
TheoremDoc Finset.image_subset_image as "Finset.image_subset_image" in "Finset"

/-- `Finset.image_mono f` proves that `Finset.image f` is monotone.

Disabled alongside `Finset.image_subset_image`.
-/
TheoremDoc Finset.image_mono as "Finset.image_mono" in "Finset"

/-- `Finset.image_union s₁ s₂` proves
`(s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f`.

Disabled to force manual image membership reasoning.
-/
TheoremDoc Finset.image_union as "Finset.image_union" in "Finset"

/-- `Finset.image_empty f` proves `(∅ : Finset α).image f = ∅`.

Disabled where image boundary cases should be proven manually.
-/
TheoremDoc Finset.image_empty as "Finset.image_empty" in "Finset"

/-- `Finset.image_singleton f a` proves `{a}.image f = {f a}`.

Disabled where image boundary cases should be proven manually.
-/
TheoremDoc Finset.image_singleton as "Finset.image_singleton" in "Finset"

/-- `Finset.image_subset_iff` states
`s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t`.

Disabled to force manual membership reasoning about images.
-/
TheoremDoc Finset.image_subset_iff as "Finset.image_subset_iff" in "Finset"

/-! ### by_contra tactic -/

/-- `by_contra h` proves the goal by contradiction. It introduces
`h : ¬ goal` and changes the goal to `False`.

## Syntax
```
by_contra h
```

## When to use it
When you need to prove something by assuming its negation and deriving
a contradiction. This is especially useful for complement reasoning:
to show `x ∈ t`, assume `x ∉ t` and derive `False`.

## Example
```
-- Goal: x ∈ t
by_contra hnt
-- hnt : x ∉ t, Goal: False
exact h.2 ⟨h.1, hnt⟩
```
-/
TacticDoc by_contra

/-! ### Cardinality-specific disabled theorems -/

/-- `Finset.card_filter_le s p` proves `(s.filter p).card ≤ s.card` directly.

Disabled in levels where the learner should compose `filter_subset` with
`card_le_card` to derive the bound manually.
-/
TheoremDoc Finset.card_filter_le as "Finset.card_filter_le" in "Card"

/-- `Finset.card_insert_le a s` proves `(insert a s).card ≤ s.card + 1`
without requiring a non-membership proof.

Disabled to force the learner to use `card_insert_of_notMem` with an
explicit non-membership argument.
-/
TheoremDoc Finset.card_insert_le as "Finset.card_insert_le" in "Card"

/-- `Finset.card_le_univ s` proves `s.card ≤ Fintype.card α` directly.

Disabled in levels where the learner should derive this bound by composing
`subset_univ` with `card_le_card` and then using `card_univ` + `card_fin`.
-/
TheoremDoc Finset.card_le_univ as "Finset.card_le_univ" in "Card"

/-- `Fintype.card_le_of_injective f hf` proves `card α ≤ card β` from
`hf : Function.Injective f`.

Disabled in pigeonhole levels where the learner should build the
cardinality argument from Finset-level tools.
-/
TheoremDoc Fintype.card_le_of_injective as "Fintype.card_le_of_injective" in "Card"

/-- `Fintype.not_injective_of_card_lt f h` proves `¬ Function.Injective f`
directly from `h : card β < card α`.

Disabled to prevent one-shotting the pigeonhole level.
-/
TheoremDoc Fintype.not_injective_of_card_lt as "Fintype.not_injective_of_card_lt" in "Card"

/-- `Fintype.surjective_of_injective` proves that for `f : α → α` on a
finite type, injectivity implies surjectivity.

Disabled in the capstone level where the learner should derive this.
-/
TheoremDoc Fintype.surjective_of_injective as "Fintype.surjective_of_injective" in "Card"

/-- `Fintype.injective_iff_surjective` proves that for `f : α → α` on a
finite type, injectivity is equivalent to surjectivity.

Disabled in the capstone level where the learner should derive this.
-/
TheoremDoc Fintype.injective_iff_surjective as "Fintype.injective_iff_surjective" in "Card"

/-- `Fintype.injective_iff_bijective` proves that for `f : α → α` on a
finite type, injectivity is equivalent to bijectivity.

Disabled in the capstone level.
-/
TheoremDoc Fintype.injective_iff_bijective as "Fintype.injective_iff_bijective" in "Card"

/-- `Fintype.surjective_iff_bijective` proves that for `f : α → α` on a
finite type, surjectivity is equivalent to bijectivity.

Disabled in the capstone level.
-/
TheoremDoc Fintype.surjective_iff_bijective as "Fintype.surjective_iff_bijective" in "Card"

/-- `Finset.map_eq_of_subset` proves `s.map f = s` when `s.map f ⊆ s`.

Disabled to prevent shortcutting the capstone proof.
-/
TheoremDoc Finset.map_eq_of_subset as "Finset.map_eq_of_subset" in "Card"

/-! ### CountingTypes-specific disabled theorems -/

/-- `Nat.descFactorial_one n` is the shortcut `n.descFactorial 1 = n`.
Disabled in levels where the learner should practice the full recursive unfolding.
-/
TheoremDoc Nat.descFactorial_one as "Nat.descFactorial_one" in "Fintype"

/-- `Nat.descFactorial_self n` states `n.descFactorial n = n!`.
Disabled in levels where the learner should practice the recursive definition.
-/
TheoremDoc Nat.descFactorial_self as "Nat.descFactorial_self" in "Fintype"

/-- `Finset.eq_of_subset_of_card_le h h₂` proves `s = t` from
`h : s ⊆ t` and `h₂ : #t ≤ #s`.

If a subset has at least as many elements as its superset,
they must be equal.

## Syntax
```
exact Finset.eq_of_subset_of_card_le h₁ h₂
```

## When to use it
When you have a subset relation `s ⊆ t` and a cardinality bound
`#t ≤ #s`, and want to conclude `s = t`.
-/
TheoremDoc Finset.eq_of_subset_of_card_le as "Finset.eq_of_subset_of_card_le" in "Card"

/-- `Finset.eq_univ_of_card s hs` proves `s = Finset.univ` from
`hs : #s = Fintype.card α`.

Disabled to force manual equality reasoning via subset + cardinality.
-/
TheoremDoc Finset.eq_univ_of_card as "Finset.eq_univ_of_card" in "Card"

/-! ### AbstractionLadder-specific disabled theorems -/

/-- `List.perm_cons_erase` states that if `a ∈ l`, then
`l ~ a :: l.erase a`. This one-shots permutation proofs.
-/
TheoremDoc List.perm_cons_erase as "List.perm_cons_erase" in "List"

/-- `List.Perm.decidable` makes permutation decidable for lists with
`DecidableEq`. This lets `decide` close permutation goals.
-/
TheoremDoc List.Perm.decidable as "List.Perm.decidable" in "List"

/-! ### Fintype-specific disabled theorems -/

/-- `Fintype.card_le_of_injective f hf` states that if `f : α → β` is
injective, then `Fintype.card α ≤ Fintype.card β`.

Disabled in levels where the learner should derive cardinality bounds
from explicit card_* lemmas rather than using injection shortcuts.
-/
TheoremDoc Fintype.card_le_of_injective as "Fintype.card_le_of_injective" in "Fintype"

/-- `Fintype.card_le_of_surjective f hf` states that if `f : α → β` is
surjective, then `Fintype.card β ≤ Fintype.card α`.

Disabled in levels where the learner should derive cardinality bounds
from explicit card_* lemmas.
-/
TheoremDoc Fintype.card_le_of_surjective as "Fintype.card_le_of_surjective" in "Fintype"

/-! ### BigOp-specific disabled theorems -/

/-- `Finset.sum_add_distrib` states that
`∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + (∑ x ∈ s, g x)`.

Sums distribute over pointwise addition (linearity of summation).

Disabled in levels where the learner should prove this by induction.
-/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "BigOp"

/-- `Finset.sum_range_sub` relates a telescoping sum to its boundary values.

Disabled in levels where the learner should prove sum identities by induction.
-/
TheoremDoc Finset.sum_range_sub as "Finset.sum_range_sub" in "BigOp"

/-- `Finset.eq_sum_range_sub` expresses a value as a telescoping sum.

Disabled in levels where the learner should prove sum identities by induction.
-/
TheoremDoc Finset.eq_sum_range_sub as "Finset.eq_sum_range_sub" in "BigOp"

/-- `Finset.prod_mul_distrib` states that
`∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * (∏ x ∈ s, g x)`.

Products distribute over pointwise multiplication.

Disabled in levels where the learner should prove this by induction.
-/
TheoremDoc Finset.prod_mul_distrib as "Finset.prod_mul_distrib" in "BigOp"

/-- `Finset.prod_const_one` states that `∏ x ∈ s, 1 = 1`.

The product of ones is one.

Disabled in levels where the learner should prove this by induction.
-/
TheoremDoc Finset.prod_const_one as "Finset.prod_const_one" in "BigOp"

/-- `Finset.prod_eq_one` states that if `f x = 1` for all `x ∈ s`,
then `∏ x ∈ s, f x = 1`.

Disabled in levels where the learner should prove product identities by induction.
-/
TheoremDoc Finset.prod_eq_one as "Finset.prod_eq_one" in "BigOp"

/-! ### Powerset-specific disabled theorems -/

/-- `Finset.empty_mem_powerset s` proves `∅ ∈ s.powerset` directly.

Disabled in levels where the learner should prove this by rewriting with
`mem_powerset` and using `empty_subset`.
-/
TheoremDoc Finset.empty_mem_powerset as "Finset.empty_mem_powerset" in "Finset"

/-- `Finset.mem_powerset_self s` proves `s ∈ s.powerset` directly.

Disabled in levels where the learner should prove this by rewriting with
`mem_powerset`.
-/
TheoremDoc Finset.mem_powerset_self as "Finset.mem_powerset_self" in "Finset"

/-- `Finset.powerset_mono` states that `s.powerset ⊆ t.powerset ↔ s ⊆ t`.

Disabled in levels where the learner should prove monotonicity manually
using `mem_powerset` and subset transitivity.
-/
TheoremDoc Finset.powerset_mono as "Finset.powerset_mono" in "Finset"

/-- Disabled: `Nat.choose_symm_add` proves `choose (n + k) n = choose (n + k) k`.
This is a direct consequence of symmetry that would bypass manual proofs. -/
TheoremDoc Nat.choose_symm_add as "Nat.choose_symm_add" in "Choose"

/-- Disabled: `Nat.choose_symm_of_eq_add` proves `choose n k = choose n (n - k)`
from an equation `n = k + j`. Bypasses manual symmetry reasoning. -/
TheoremDoc Nat.choose_symm_of_eq_add as "Nat.choose_symm_of_eq_add" in "Choose"

/-- Disabled: `Nat.choose_succ_self_right` proves `choose n (n + 1) = 0`.
Trivializes boundary-value exercises. -/
TheoremDoc Nat.choose_succ_self_right as "Nat.choose_succ_self_right" in "Choose"

/-- Disabled: `Nat.choose_eq_one_iff` characterizes when `choose n k = 1`.
Trivializes boundary-value exercises. -/
TheoremDoc Nat.choose_eq_one_iff as "Nat.choose_eq_one_iff" in "Choose"

/-- `Nat.choose_two_right` gives the closed form for choosing 2:

`Nat.choose n 2 = n * (n - 1) / 2`

This is the formula C(n, 2) = n(n-1)/2.

## Syntax
```
rw [Nat.choose_two_right]
```

## When to use it
When the goal involves `n.choose 2` and you want to work with
the explicit formula.

## Connection to offDiag
Since `offDiag_card` gives n^2 - n and `choose_two_right`
gives n(n-1)/2, the identity offDiag.card = 2 * C(n, 2)
bridges ordered and unordered pair counting.

## Note
Disabled in BinomialCoefficients (where the induction proof
is the lesson). Introduced in Products.
-/
TheoremDoc Nat.choose_two_right as "Nat.choose_two_right" in "Choose"

/-- `Finset.card_product s t` states that
`(s ×ˢ t).card = s.card * t.card`.

This is the **multiplication principle**: the number of pairs
is the product of the individual counts.

## Syntax
```
have h := Finset.card_product s t
```

## When to use it
When the goal involves the cardinality of a product `s ×ˢ t`.

## Notation
`s ×ˢ t` is typed as `\x\^s` or `\times\^s`.
-/
TheoremDoc Finset.card_product as "Finset.card_product" in "Card"

/-! ### Products-specific disabled theorems -/

/-- `Finset.product_subset_product` proves `s ×ˢ t ⊆ s' ×ˢ t'`
from `s ⊆ s'` and `t ⊆ t'`.

Disabled to force the learner to use `mem_product` extraction
and `mk_mem_product` construction manually.
-/
TheoremDoc Finset.product_subset_product as "Finset.product_subset_product" in "Product"

/-- `Finset.product_subset_product_left` proves `s ×ˢ t ⊆ s' ×ˢ t`
from `s ⊆ s'`.
-/
TheoremDoc Finset.product_subset_product_left as "Finset.product_subset_product_left" in "Product"

/-- `Finset.product_subset_product_right` proves `s ×ˢ t ⊆ s ×ˢ t'`
from `t ⊆ t'`.
-/
TheoremDoc Finset.product_subset_product_right as "Finset.product_subset_product_right" in "Product"

/-! ### Finsupp theorems disabled in level files -/

/-- `Finsupp.single_apply` is the unified evaluation lemma:

`Finsupp.single_apply : Finsupp.single a b a' = if a = a' then b else 0`

## Syntax
```
rw [Finsupp.single_apply]
```

## Relationship to other lemmas
- `single_eq_same` is `single_apply` with `a' = a` (the `if` is true)
- `single_eq_of_ne` is `single_apply` with `a' ≠ a` (the `if` is false)

## When to use it
When you want to expose the `if-then-else` structure of a `single`
evaluation. In most cases, `single_eq_same` or `single_eq_of_ne`
are more convenient.

In this world, `single_apply` is disabled in most levels to encourage
you to reason about each case explicitly using the specialized lemmas.
-/
TheoremDoc Finsupp.single_apply as "Finsupp.single_apply" in "Finsupp"

/-- `Finsupp.single_add` says that a single with a summed value
equals the sum of two singles:

`Finsupp.single_add : Finsupp.single a (b₁ + b₂) = Finsupp.single a b₁ + Finsupp.single a b₂`

## Syntax
```
rw [Finsupp.single_add]         -- expand one single into a sum
rw [← Finsupp.single_add]      -- combine two singles into one
```

## When to use it
- **Forward** (`rw [single_add]`): when you want to expand
  `single a (b₁ + b₂)` into a sum of two singles.
- **Backward** (`rw [← single_add]`): when you want to combine
  `single a b₁ + single a b₂` into a single with summed value.
  This is the more common direction.

## Warning
Both singles must have the **same** first argument `a`.
This lemma does not apply to singles at different positions.

In this world, `single_add` is disabled in levels that teach pointwise
evaluation, so you learn to compute values manually before using the
algebraic shortcut.
-/
TheoremDoc Finsupp.single_add as "Finsupp.single_add" in "Finsupp"
