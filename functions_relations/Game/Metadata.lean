import GameServer
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Prod
import Mathlib.Algebra.Group.Nat.Even
-- import Mathlib.Tactic.Push  -- for push_neg, added when needed

/-! ## NNG4-baseline tactic documentation

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

## Warning
`rw` replaces ALL occurrences of the pattern, not just the first.
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

/-- `cases x with | constructor₁ args | constructor₂ args` performs
case analysis on `x`, creating one subgoal per constructor.

## Syntax
```
-- single constructor (e.g., ∃):
cases h with | intro x hx

-- multiple constructors (e.g., ∨):
cases h with | inl h₁ | inr h₂

-- natural numbers:
cases n with | zero | succ m
```

Each constructor names create a new subgoal that you handle
one at a time.

## When to use it
When you want to consider all possible forms of a value (e.g.,
`∨` has `inl` and `inr`, `∃` has `intro`).
-/
TacticDoc cases

/-- `constructor` splits a goal with a single constructor (like `∧` or `↔`)
into its components.

## Syntax
```
constructor
```

## When to use it
When the goal is `P ∧ Q` (splits into `P` and `Q`), `P ↔ Q`
(splits into `P → Q` and `Q → P`), or `True` (closes immediately).
-/
TacticDoc constructor

/-- `assumption` closes the goal if a hypothesis in the context has
exactly the right type.

## Syntax
```
assumption
```

## When to use it
When a hypothesis matches the goal.
-/
TacticDoc assumption

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

/-- `omega` solves linear arithmetic goals over `ℕ` and `ℤ`.
It handles equalities, inequalities, and disequalities involving
addition, subtraction, and multiplication by literals.

## Syntax
```
omega
```

## When to use it
When the goal is a concrete numeric fact like `3 < 5` or `n + 1 ≤ m`,
or when hypotheses combine to yield the goal by linear arithmetic.

## Warning
`omega` only handles *linear* arithmetic. It cannot solve goals
involving multiplication of variables.
-/
TacticDoc omega

/-- `rfl` closes a goal of the form `a = a` (reflexivity).

## Syntax
```
rfl
```

## When to use it
When both sides of an equality are definitionally equal.
-/
TacticDoc rfl

/-- `apply e` reduces the goal by applying `e`, leaving any
remaining arguments as new goals.

## Syntax
```
apply e
```

## When to use it
When the goal matches the conclusion of some known fact `e`.
After `apply e`, the remaining goals are the premises of `e`.
-/
TacticDoc apply

/-- `induction x with | case args` performs structural induction on `x`.

## Syntax
```
-- natural number induction:
induction n with | zero | succ m ih

-- list induction:
induction xs with | nil | cons x xs ih
```

Each case creates a separate subgoal that you handle one at a time.
The `ih` variable is the induction hypothesis.

## When to use it
When you need to prove a statement for all natural numbers
(or elements of another inductive type) by induction.
-/
TacticDoc induction

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

/-- `contradiction` closes the goal by finding a contradiction among the
hypotheses. It can detect:

- `h₁ : P` and `h₂ : ¬ P`
- `h : False`
- `h : n < n` or other impossible arithmetic
- Definitionally impossible hypotheses (e.g., set membership that
  reduces to a false statement)

## Syntax
```
contradiction
```

## When to use it
When your hypotheses contain a contradiction. `contradiction` is
more powerful than `exact h` because it can see through definitional
wrappers — for example, it can detect that `h : 7 ∈ {n | n < 5}`
is impossible, even though `omega` cannot.
-/
TacticDoc contradiction

/-- `Set.mem_setOf_eq` states `x ∈ {a | p a} = p x` — membership in a
set-builder set equals the predicate applied to the element.

This theorem is disabled in early levels because the course teaches `show`
as the primary method for unfolding set membership.
-/
TheoremDoc Set.mem_setOf_eq as "Set.mem_setOf_eq" in "Set"

/-- `Set.mem_setOf` states `x ∈ {a | p a} ↔ p x` — the iff version
of set-builder membership unfolding.

Disabled for the same reason as `Set.mem_setOf_eq`.
-/
TheoremDoc Set.mem_setOf as "Set.mem_setOf" in "Set"

/-- `Set.mem_image_of_mem f h` states that if `h : a ∈ s`, then
`f a ∈ f '' s`. It directly constructs image membership from source
membership.

Disabled in image levels to force the learner to construct the
witness manually using `use` and `exact ⟨x, hx, rfl⟩`.
-/
TheoremDoc Set.mem_image_of_mem as "Set.mem_image_of_mem" in "Set"

/-- `Or.inl h` constructs a proof of `P ∨ Q` from a proof `h : P`.
It chooses the LEFT disjunct.

## When to use it
When building anonymous constructors for unions: if `hx : x ∈ s`,
then `Or.inl hx : x ∈ s ∨ x ∈ t` (equivalently `x ∈ s ∪ t`).

## Example
```
-- hx : x ∈ s, Goal: ∃ z ∈ s ∪ t, f z = f x
exact ⟨x, Or.inl hx, rfl⟩
```

## Alternative
The `left` tactic followed by `exact hx` achieves the same result.
-/
TheoremDoc Or.inl as "Or.inl" in "Logic"

/-- `Or.inr h` constructs a proof of `P ∨ Q` from a proof `h : Q`.
It chooses the RIGHT disjunct.

## When to use it
When building anonymous constructors for unions: if `hx : x ∈ t`,
then `Or.inr hx : x ∈ s ∨ x ∈ t` (equivalently `x ∈ s ∪ t`).

## Example
```
-- hx : x ∈ t, Goal: ∃ z ∈ s ∪ t, f z = f x
exact ⟨x, Or.inr hx, rfl⟩
```

## Alternative
The `right` tactic followed by `exact hx` achieves the same result.
-/
TheoremDoc Or.inr as "Or.inr" in "Logic"

/-! ## Baseline disabled tactic documentation

These tactics are disabled globally because they close goals that
the player should learn to handle manually.
-/

/-- `trivial` attempts to close the goal using a combination of
basic tactics (`rfl`, `exact True.intro`, `assumption`).

Disabled because it bypasses the learning of specific proof steps.
-/
TacticDoc trivial

/-- `decide` closes goals that are decidable propositions by
evaluating them computationally.

Disabled because it bypasses manual reasoning.
-/
TacticDoc «decide»

/-- `native_decide` is like `decide` but uses native code evaluation
for faster computation.

Disabled for the same reason as `decide`.
-/
TacticDoc native_decide

/-- `simp` applies a set of simplification lemmas to the goal
and hypotheses.

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

/-- `tauto` closes goals that are propositional tautologies. It handles
`∨`, `∧`, `→`, `¬`, `↔`, `True`, `False`.

Disabled in levels where the learner should construct proofs manually.
-/
TacticDoc tauto

/-- `norm_num` evaluates numerical expressions and closes arithmetic
goals that can be decided by computation.

Disabled in levels where manual arithmetic reasoning is the lesson.
-/
TacticDoc norm_num

/-- `linarith` closes goals that are linear arithmetic consequences
of hypotheses. It handles inequalities and equalities over ordered
fields and rings.

Disabled in levels where manual reasoning is the lesson.
-/
TacticDoc linarith

/-- `Iff.rfl` is the reflexivity proof for biconditionals: `P ↔ P`.

It can close any goal of the form `P ↔ P` where both sides are
definitionally equal. Disabled in levels where the learner should
prove each direction explicitly.
-/
TheoremDoc Iff.rfl as "Iff.rfl" in "Logic"

/-- `show P` converts the goal to `P`, as long as `P` is
definitionally equal to the current goal.

## Syntax
```
show P
```

## When to use it
When the goal is correct but in a form that other tactics cannot
parse. For example, `x ∈ {n | n < 5}` is definitionally `x < 5`,
but `omega` needs the arithmetic form. Use `show x < 5` to convert.

## Example
```
-- Goal: 3 ∈ {n | n < 5}
show 3 < 5
-- Goal: 3 < 5
omega
```

## Warning
`show` does NOT prove anything — it only changes the display.
The new goal must be definitionally equal to the old one, or
Lean will reject the `show`.
-/
TacticDoc «show»

/-- `fin_cases h` performs case analysis on a `Fin n` or other
finite type hypothesis, creating one subgoal per value.

## Syntax
```
fin_cases h
```

## When to use it
When `h : Fin n` and you want to check each value `0, 1, ..., n-1`
individually. This can one-shot many proofs about small finite types.

Disabled in levels that require manual reasoning about finite indices.
-/
TacticDoc fin_cases

/-- `by_contra h` assumes `¬ goal` and changes the goal to `False`.

## Syntax
```
by_contra h
```

## When to use it
When you cannot prove the goal directly but can derive a contradiction
from its negation. This is classical reasoning.

## Example
```
-- Goal: ∃ i, P i
by_contra h
-- h : ¬ ∃ i, P i
-- Goal: False
```
-/
TacticDoc by_contra

/-- `push_neg` pushes negation inward through quantifiers and
connectives: `¬∀` becomes `∃¬`, `¬∃` becomes `∀¬`, `¬(a < b)` becomes
`b ≤ a`, etc.

## Syntax
```
push_neg            -- on the goal
push_neg at h       -- on a hypothesis
```

## When to use it
When you have a negated statement and need to work with its
positive form.

Disabled in levels where you should see what push_neg does manually.
-/
TacticDoc push_neg

/-- `mono` attempts to prove monotonicity goals by automatically applying
relevant monotonicity lemmas.

Disabled to prevent one-shot solutions to subset and image problems.
-/
TacticDoc mono

/-- `gcongr` proves goals using generalized congruence — it applies
congruence and monotonicity lemmas to reduce inequalities and subset goals.

Disabled to prevent one-shot solutions to subset and image problems.
-/
TacticDoc gcongr

/-! ## Image-related tactic documentation

These tactics are taught in ImageWorld but their docs are kept here
to avoid duplicate TacticDoc declarations across levels.
-/

/-- `obtain ⟨x, hx⟩ := h` destructures hypothesis `h` into components
using the same pattern syntax as `rcases`.

## Syntax
```
obtain ⟨x, hx⟩ := h              -- existential
obtain ⟨h₁, h₂⟩ := h             -- conjunction
obtain ⟨x, hx, rfl⟩ := h         -- with substitution
```

## When to use it
When you have a hypothesis with structure (`∃`, `∧`) and want to
extract its components. Like `rcases`, but does not support `|`
for disjunctions.

## Example
```
-- hy : y ∈ f '' s
obtain ⟨x, hx, hfx⟩ := hy
-- x : α, hx : x ∈ s, hfx : f x = y
```

## Tip
Use `rfl` inside the pattern to substitute equations automatically:
`obtain ⟨x, hx, rfl⟩ := hy` replaces `y` with `f x` everywhere.
-/
TacticDoc obtain

/-- `rintro` combines `intro` with pattern matching in one step.
The `rfl` pattern automatically substitutes equations.

## Syntax
```
rintro ⟨x, hx, rfl⟩      -- existential + conjunction + substitution
rintro (h | h)             -- disjunction (two cases)
rintro ⟨h₁, h₂⟩           -- conjunction
rintro x ⟨a, ha, rfl⟩     -- introduce variable then destructure
```

## Angle bracket input
Type ⟨ as `\<` and ⟩ as `\>` in the editor.

## When to use it
When the goal starts with `∀` or `→` and you want to immediately
destructure the introduced hypothesis. Especially useful for image
membership: `rintro ⟨x, hx, rfl⟩` replaces `intro hy` +
`obtain ⟨x, hx, hfx⟩ := hy` + `rw [← hfx]`.

## Example
```
-- Goal: ∀ y, y ∈ f '' s → P y
rintro y ⟨x, hx, rfl⟩
-- x : α, hx : x ∈ s, Goal: P (f x)
```

## Warning
The `rfl` pattern substitutes a variable everywhere. Make sure
the variable you are eliminating is the one you intend.
-/
TacticDoc rintro

/-- `rcases h with pattern` destructures hypothesis `h` using the
same pattern syntax as `rintro`. It supports disjunctions via `|`.

## Syntax
```
rcases h with ⟨x, hx⟩           -- existential
rcases h with ⟨h₁, h₂⟩          -- conjunction
rcases h with h₁ | h₂            -- disjunction (creates two goals)
rcases h with ⟨x, hx, rfl⟩      -- with substitution
rcases h with ⟨x, hx⟩ | ⟨y, hy⟩ -- nested disjunction
```

## When to use it
When you have a hypothesis with structure (`∃`, `∧`, `∨`) and want
to destructure it. For non-disjunctive patterns, `obtain` works
the same way. The advantage of `rcases` is disjunction support.

## Example
```
-- h : y ∈ f '' s ∪ f '' t
rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
-- Two goals: one for f '' s, one for f '' t
```
-/
TacticDoc rcases
