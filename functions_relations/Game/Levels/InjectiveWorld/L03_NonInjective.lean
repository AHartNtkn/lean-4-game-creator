import Game.Metadata

World "InjectiveWorld"
Level 3

Title "A Non-Injective Function"

TheoremTab "Function"

Introduction "
# Disproving Injectivity

Not every function is injective. The function `n ↦ n / 2` on ℕ
(integer division) sends both 0 and 1 to 0:

$$0 / 2 = 0 \\quad\\text{and}\\quad 1 / 2 = 0$$

So `f 0 = f 1` but `0 \\neq 1` — this violates injectivity.

**The proof shape for ¬ Injective f**:

To prove `¬ P` (for any proposition `P`), recall that `¬ P` means `P → False`.
So you `intro h` to assume `P`, then derive `False`.

For `¬ Injective f`:
1. `intro h` — assume `h : Injective f`
2. Use `h` with two specific inputs that map to the same output
3. Get a false equation like `0 = 1`
4. Derive a contradiction

**Your task**: Prove `¬ Function.Injective (fun n : ℕ => n / 2)`.

The counterexample is `a = 0`, `b = 1`: both satisfy `a / 2 = 0 = b / 2`,
but `0 ≠ 1`.
"

/-- Integer division by 2 is not injective on ℕ. -/
Statement : ¬ Function.Injective (fun n : ℕ => n / 2) := by
  Hint "Since `¬ P` means `P → False`, start with `intro h` to assume
  injectivity and aim for a contradiction."
  intro h
  Hint "Now `h : Function.Injective (fun n => n / 2)` says that if
  `a / 2 = b / 2`, then `a = b`. We know `0 / 2 = 0 = 1 / 2`, so
  applying `h` with `a = 0` and `b = 1` gives `0 = 1`.

  Create this false equation: `have key : (0 : ℕ) = 1 := by ...`
  where the proof uses `apply h` then shows `0 / 2 = 1 / 2`."
  Hint (hidden := true) "Try:
  `have key : (0 : ℕ) = 1 := by apply h; rfl`
  then `omega`."
  have key : (0 : ℕ) = 1 := by
    Hint "The goal is `0 = 1`. But we can get this from `h`: if we show
    `(fun n => n / 2) 0 = (fun n => n / 2) 1` (i.e., `0 / 2 = 1 / 2`),
    then `h` gives us `0 = 1`. Use `apply h`."
    apply h
    Hint "The goal is now `(fun n => n / 2) 0 = (fun n => n / 2) 1`,
    which reduces to `0 / 2 = 1 / 2`, i.e., `0 = 0`. Use `rfl`."
    rfl
  Hint "You have `key : 0 = 1` — a contradiction! Use `omega` to
  close the goal `False`."
  omega

Conclusion "
You disproved injectivity by finding a counterexample!

**The proof had three parts**:
1. `intro h` — assume injectivity
2. `have key : 0 = 1` — apply injectivity to a colliding pair
3. `omega` — `0 = 1` is absurd, so `False`

**Two proof shapes side by side**:

| Proving `Injective f` | Proving `¬ Injective f` |
|---|---|
| `intro a b hab` | `intro h` |
| Show `a = b` from `hab` | Find `a ≠ b` with `f a = f b` |
| Constructive | By contradiction |

**Why `rfl` works**: `0 / 2 = 0` and `1 / 2 = 0` in ℕ (integer division
rounds down). So `0 / 2 = 1 / 2` is `0 = 0`, which is `rfl`.

**Why non-injectivity matters**: A non-injective function **loses
information** — distinct inputs become indistinguishable after applying
`f`. You cannot recover the original input from the output. In fact,
`n / 2` has no left inverse (no function `g` with `g (n / 2) = n` for
all `n`), precisely because the information is lost. You will prove
the connection between left inverses and injectivity in Level 7.

**Looking ahead**: You have now mastered both directions — proving AND
disproving injectivity. Next, you will learn how injectivity behaves
under function composition.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
