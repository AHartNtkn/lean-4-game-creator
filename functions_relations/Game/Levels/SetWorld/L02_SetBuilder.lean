import Game.Metadata

World "SetWorld"
Level 2

Title "Set Builder Notation"

Introduction "
# Set Builder Notation

In mathematics, you write sets like $\\{n \\in \\mathbb{N} \\mid n < 5\\}$.
In Lean, this becomes `{n : ℕ | n < 5}`.

This notation is syntactic sugar for `setOf (fun n => n < 5)`, which is
defined as... just `fun n => n < 5` itself! The function `setOf` is
literally the identity: it takes a predicate and returns it as a `Set`.

So what happens when you check membership?

$$3 \\in \\{n \\mid n < 5\\} = (\\text{fun } n \\Rightarrow n < 5) \\; 3 = 3 < 5$$

The set builder notation just wraps a predicate. Membership evaluates
the predicate at the given point.

**Look at your goal**: it says `3 ∈ {n | n < 5}`. We know this is
*definitionally* equal to `3 < 5`, but some tactics (like `omega`)
need the goal in explicit arithmetic form to work.

The `show` tactic converts the goal to a definitionally equal form.
Try `show 3 < 5` — this tells Lean to display the goal as `3 < 5`
(which it can verify is the same thing). Then `omega` closes it.

**Your task**: Use `show 3 < 5` then `omega`.
"

/-- Prove that 3 belongs to the set of naturals less than 5. -/
Statement : (3 : ℕ) ∈ {n : ℕ | n < 5} := by
  Hint "Use `show 3 < 5` to convert the goal to arithmetic form.
  This works because membership in the set-builder set
  is definitionally equal to `3 < 5`."
  Hint (hidden := true) "After `show 3 < 5`, use `omega` to close
  the arithmetic goal."
  show 3 < 5
  Hint "`omega` can now see the goal `3 < 5` and close it."
  omega

Conclusion "
You used `show 3 < 5` to convert the goal, then `omega` to close it.

The chain of definitional reductions that `show` verified:
1. `3 ∈ {n | n < 5}` — the original statement
2. `3 ∈ setOf (fun n => n < 5)` — notation expansion
3. `(fun n => n < 5) 3` — membership is function application
4. `3 < 5` — beta reduction

**`show` is a general tool**, not just an arithmetic trick. It works
whenever two expressions are *definitionally equal* — meaning Lean can
verify they are the same by unfolding definitions, without needing a
proof. You will use `show` throughout this course to unfold set
membership, complement membership, preimage membership, and more.
The pattern is always the same: `show` reveals the predicate content
hidden inside set-theoretic notation.

This is the core pattern you will use throughout this course:
**set membership questions reduce to predicate questions**.

When you see `x ∈ {y | P y}`, you can always think of it as `P x`.
"

/-- `setOf p` creates the set `{x | p x}` from a predicate `p : α → Prop`.

The notation `{x | p x}` or `{x : α | p x}` is syntactic sugar for
`setOf (fun x => p x)`.

Since `Set α = α → Prop` and `setOf p = p`, the set builder notation
is really just wrapping a predicate.

## Syntax
```
{x : α | P x}     -- set of elements satisfying P
{x | P x}         -- type inferred from context
```

## Example
`{n : ℕ | n < 5}` is the set of natural numbers less than 5.
`3 ∈ {n : ℕ | n < 5}` reduces to `3 < 5`.

## Warning
The variable after `{` is a *binder* — it is local to the expression
after `|`. Writing `{n | n < 5}` defines a predicate; `n` does not
refer to any `n` in the surrounding context.
-/
DefinitionDoc setOf as "setOf"

NewTactic «show»
NewDefinition setOf

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
