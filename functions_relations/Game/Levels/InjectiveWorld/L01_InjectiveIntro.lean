import Game.Metadata

World "InjectiveWorld"
Level 1

Title "The Injectivity Proof Shape"

TheoremTab "Function"

Introduction "
# Injective Functions

A function `f` is **injective** (one-to-one) if distinct inputs always
produce distinct outputs. Equivalently: if `f a = f b`, then `a = b`.

In Lean, this is `Function.Injective f`:

$$\\text{Injective}(f) \\;\\;:\\equiv\\;\\; \\forall\\, a\\, b,\\;\\; f(a) = f(b) \\;\\Longrightarrow\\; a = b$$

**The canonical proof shape**: To prove `Injective f`, you always start the
same way:

```
intro a b hab
```

This gives you `a b : α` and `hab : f a = f b`. Your job is to derive
`a = b`.

**Your task**: Prove that the successor function `n ↦ n + 1` on ℕ is
injective.

After `intro a b hab`, the hypothesis `hab` says `a + 1 = b + 1`
(definitionally — Lean sees through the lambda). But `omega` cannot read
the lambda form directly. Use `have h : a + 1 = b + 1 := hab` to create
a version that `omega` can work with.
"

/-- The successor function n ↦ n + 1 is injective. -/
Statement : Function.Injective (fun n : ℕ => n + 1) := by
  Hint "Start with `intro a b hab` to get the canonical injectivity
  setup: two inputs `a` and `b`, and the hypothesis `hab` that they
  produce the same output."
  intro a b hab
  Hint "The hypothesis `hab` says `(fun n => n + 1) a = (fun n => n + 1) b`,
  which is definitionally `a + 1 = b + 1`. However, `omega` cannot see
  through the lambda notation. Create a named version:
  `have h : a + 1 = b + 1 := hab`"
  Hint (hidden := true) "`have h : a + 1 = b + 1 := hab` then `omega`."
  Branch
    have h : a + 1 = b + 1 := hab
    Hint "Now `h : a + 1 = b + 1` is in your context. Since the goal is
    `a = b`, use `omega` to derive it from the arithmetic equation."
    omega
  change a + 1 = b + 1 at hab
  omega

Conclusion "
You proved your first injectivity! The canonical proof shape is:

```
intro a b hab       -- assume f a = f b
have h : ... := hab -- extract the arithmetic equation
omega               -- derive a = b
```

**The key pattern**: Every injectivity proof starts with `intro a b hab`.
What comes next depends on the function — for arithmetic functions,
`omega` finishes the job once you expose the equation.

**Alternative**: Instead of `have`, you can rewrite the hypothesis in
place using `change a + 1 = b + 1 at hab` (the `change` tactic replaces
a goal or hypothesis with a definitionally equal expression — you will
encounter it in later worlds). Both approaches make the equation
visible to `omega`.

**Why does `omega` need help?** The hypothesis `hab` has type
`(fun n => n + 1) a = (fun n => n + 1) b` — a lambda application.
Lean knows this equals `a + 1 = b + 1` by definition, but `omega`
only processes explicit arithmetic. The `have` or `change` step
bridges this gap.
"

/-- `Function.Injective f`, written `Function.Injective f`, means
that `f` maps distinct inputs to distinct outputs:

$$\forall\, a_1\, a_2,\;\; f(a_1) = f(a_2) \;\Longrightarrow\; a_1 = a_2$$

## Syntax
```
hinj : Function.Injective f
hinj hab : a = b      -- from hab : f a = f b
```

## When to use it
When you have `f a = f b` and need `a = b`. Apply the injectivity
hypothesis to the equation.

## Example
```
-- hinj : Function.Injective f, hab : f a = f b
have h := hinj hab    -- h : a = b
```

## Warning
Injectivity is about the FUNCTION, not a specific equation. You
need a hypothesis `Function.Injective f` in scope.
-/
DefinitionDoc Function.Injective as "Function.Injective"

NewDefinition Function.Injective

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith injection
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Nat.succ_injective Nat.succ.inj Nat.add_right_cancel Nat.add_left_cancel
