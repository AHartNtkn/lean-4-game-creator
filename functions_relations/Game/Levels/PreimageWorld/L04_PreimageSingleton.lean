import Game.Metadata

World "PreimageWorld"
Level 4

Title "Preimage of a Singleton: Fibers"

TheoremTab "Set"

Introduction "
# Fibers: Preimage of a Single Point

The preimage of a **singleton** set `{y}` under `f` is called
the **fiber** of `f` over `y`:

$$f^{-1}(\\{y\\}) = \\{x \\mid f(x) = y\\}$$

The fiber over `y` is the set of ALL inputs that map to `y`.
This concept is fundamental:
- `f` is **injective** iff every fiber has at most one element
- `f` is **surjective** iff every fiber is nonempty

For the function `n \\mapsto n + 1`:
- The fiber over 3 is `{2}` (only 2 maps to 3)
- The fiber over 3 does NOT contain 5 (since `5 + 1 = 6 \\neq 3`)

**Your task**: Prove that 2 is in the fiber over 3, and 5 is not.

**Proof plan**:
1. `constructor` — split the conjunction
2. First part: `show 2 + 1 = 3` then `omega`
3. Second part: `show \\neg (5 + 1 = 3)` then `omega`
"

/-- 2 is in the fiber over 3 (since 2+1=3), but 5 is not (since 5+1=6). -/
Statement : (2 : ℕ) ∈ (fun n : ℕ => n + 1) ⁻¹' {3} ∧
            (5 : ℕ) ∉ (fun n : ℕ => n + 1) ⁻¹' {3} := by
  Hint "Use `constructor` to split the conjunction into two goals."
  constructor
  · Hint "The goal says `2 ∈ (fun n => n + 1) ⁻¹' ..3..`. By
    preimage membership, this means `(fun n => n + 1) 2 ∈ ..3..`,
    which is `2 + 1 = 3`. Use `show 2 + 1 = 3` to make this explicit."
    Hint (hidden := true) "`show 2 + 1 = 3` then `omega`."
    show 2 + 1 = 3
    omega
  · Hint "The goal says `5 \\notin (fun n => n + 1) ⁻¹' ..3..`.
    This means `\\neg (5 + 1 = 3)`, i.e., `6 \\neq 3`.
    Use `show \\neg (5 + 1 = 3)` to make this explicit."
    Hint (hidden := true) "`show \\neg (5 + 1 = 3)` then `omega`."
    show ¬ (5 + 1 = 3)
    omega

Conclusion "
You proved that 2 is in the fiber of `n \\mapsto n + 1` over 3, but
5 is not. The fiber is just a preimage of a singleton — nothing new
mathematically, but the vocabulary is important.

**Fiber vocabulary**:
- `f ⁻¹' ..y..` is the **fiber** of `f` over `y`
- An element `x` is in the fiber iff `f x = y`
- For injective functions, each fiber has at most one element
- For surjective functions, every fiber is nonempty

The function `n \\mapsto n + 1` is injective (each fiber is a
singleton), so knowing which fiber an element belongs to tells you
exactly which element it is. For the constant function from
Level 3, every fiber is either all of `\\mathbb{N}` or empty — very
different behavior!

**Foreshadowing**: In Injective World and Surjective World, fibers
will be the key concept. Injectivity means `f ⁻¹' ..y..` has at most
one element for all `y`. Surjectivity means `f ⁻¹' ..y..` is
nonempty for all `y`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
