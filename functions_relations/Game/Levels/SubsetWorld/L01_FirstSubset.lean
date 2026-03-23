import Game.Metadata

World "SubsetWorld"
Level 1

Title "First Subset Proof"

TheoremTab "Set"

Introduction "
# Subsets: The ⊆ Relation

In mathematics, $A \\subseteq B$ means every element of $A$ is also an
element of $B$. In Lean, this is exactly what it means:

$$s \\subseteq t \\;\\;\\Longleftrightarrow\\;\\; \\forall\\, x,\\; x \\in s \\to x \\in t$$

So a subset proof has the shape: **introduce** an arbitrary element `x`
and a hypothesis `hx` that `x ∈ s`, then **show** that `x ∈ t`.

After `intro x hx`, you will have:
- `hx : x ∈ {n | n < 3}` — this is `x < 3` wrapped in set notation
- Goal: `x ∈ {n | n < 5}` — this is `x < 5` wrapped in set notation

Both are wrapped in set notation. You already know `show` for
converting the goal to an equivalent form — use `show x < 5` to
unwrap the goal. For the hypothesis, you can use `have` to extract
the arithmetic: `have h : x < 3 := hx` creates a clean arithmetic
hypothesis that `omega` can read.

**Proof plan**:
1. `intro x hx` — fix an element and assume it is in the smaller set
2. `have h : x < 3 := hx` — extract the arithmetic content of `hx`
3. `show x < 5` — unwrap the set membership on the goal
4. `omega` — derive `x < 5` from `x < 3`
"

/-- Every number less than 3 is also less than 5. -/
Statement : {n : ℕ | n < 3} ⊆ {n | n < 5} := by
  Hint "The goal is `s ⊆ t`, which means `∀ x, x ∈ s → x ∈ t`.
  Use `intro x hx` to introduce the element and the membership assumption."
  intro x hx
  Hint "Now `hx` says `x` is in the left set, but the arithmetic fact
  `x < 3` is hidden inside the set notation. Use
  `have h : x < 3 := hx` to extract it into a clean hypothesis."
  Hint (hidden := true) "`have h : x < 3 := hx` creates `h : x < 3`
  from `hx`. Then `show x < 5` unwraps the goal and `omega` closes it."
  have h : x < 3 := hx
  Hint "Good — you now have `h : x < 3`. The goal is still in
  set-notation form. Use `show x < 5` to unwrap it."
  show x < 5
  Hint "`omega` can now see both `h : x < 3` and the goal `x < 5`."
  omega

Conclusion "
You just proved your first subset relation! The proof shape was:

1. `intro x hx` — introduce element and membership hypothesis
2. `have h : x < 3 := hx` — extract the arithmetic from `hx`
3. `show x < 5` — unwrap the goal from set notation to arithmetic
4. `omega` — close the arithmetic goal

This pattern — **intro, unwrap, prove** — is the standard shape for
every `⊆` proof. The `intro x hx` step is universal; the unwrapping
and closing steps depend on the specific sets.

Using `have` to extract hypothesis content works, but it is a bit
verbose — you need to write out the type explicitly. In the next
level, you will learn `change`, a tactic designed specifically for
this unwrapping job.

**`⊆` vs `∈` — a common confusion**: These are fundamentally different
relations. `s ⊆ t` relates two *sets* and says every element of `s`
is also in `t`. `x ∈ s` relates an *element* and a *set* and says
`x` belongs to `s`. In Lean, the types enforce this: `s ⊆ t` requires
`s t : Set α`, while `x ∈ s` requires `x : α`. If you are ever unsure,
check the types: are you relating two sets, or an element to a set?

**Note on asymmetry**: We proved `{n | n < 3} ⊆ {n | n < 5}`, but the
reverse `{n | n < 5} ⊆ {n | n < 3}` is **false** — the number 4 is in
the right set but not the left. You will prove this formally in
Level 7. So `⊆` has a *direction*: unlike equality, `s ⊆ t` does
not imply `t ⊆ s`. This makes `⊆` a one-way relationship, which
we will explore further in this world.
"

/-- `⊆` (typed `\\sub` or `\\subseteq`) is the subset relation.

For sets `s t : Set α`, the statement `s ⊆ t` means:
$$\\forall\\, x,\\; x \\in s \\to x \\in t$$

## Proof strategy
To prove `s ⊆ t`:
1. `intro x hx` — introduce element `x` and hypothesis `hx : x ∈ s`
2. Show that `x ∈ t` using `hx` and any other available facts

## Syntax
```
s ⊆ t     -- s is a subset of t (\\sub or \\subseteq)
```

## Example
To prove `{n | n < 3} ⊆ {n | n < 5}`: after `intro x hx`,
unwrap the goal with `show x < 5` and close with `omega`.

## Warning
`⊆` is a *proposition* (a statement that may or may not be true),
not an operation that produces a new set.
-/
DefinitionDoc Set.Subset as "Set.Subset"

NewDefinition Set.Subset

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
