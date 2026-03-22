import Game.Metadata

World "MeetFin"
Level 3

Title "The Upper Bound"

Introduction "
# Fin 5 Does Not Contain 5

The most common misconception about `Fin n` is confusing
$\\{0, 1, \\ldots, n-1\\}$ with $\\{0, 1, \\ldots, n\\}$. The elements
of `Fin 5` are $\\{0, 1, 2, 3, 4\\}$ — **not** $\\{0, 1, 2, 3, 4, 5\\}$.

Let's make this concrete: no element of `Fin 5` has value `5`.

**Strategy**: Introduce `x` and assume `h : x.val = 5` for
contradiction. Then use `x.isLt` (which says `x.val < 5`) to get a
contradiction with `h` via `omega`.

Step by step:
1. `intro x` — introduces the element
2. `intro h` — assumes `x.val = 5` (since `≠` means `= → False`)
3. `have hlt := x.isLt` — extracts the bound `x.val < 5`
4. `omega` — sees `x.val = 5` and `x.val < 5` are contradictory
"

/-- No element of `Fin 5` has value `5`. -/
Statement : ∀ x : Fin 5, x.val ≠ 5 := by
  Hint "Start with `intro x` to introduce the element, then `intro h`
  to assume `x.val = 5` for contradiction."
  intro x
  intro h
  Hint "Now extract the bound proof: `have hlt := x.isLt`. This gives
  `hlt : x.val < 5`."
  have hlt := x.isLt
  Hint "You have `{h}` saying `x.val = 5` and `{hlt}` saying
  `x.val < 5`. These contradict each other — `omega` sees this."
  omega

Conclusion "
You've now proved what the introduction warned about: `Fin 5` contains
$\\{0, 1, 2, 3, 4\\}$ and **not** 5.

The key ingredient was `.isLt`: every `x : Fin n` carries a proof
that `x.val < n`. Combined with the assumption `x.val = n`, you get
a contradiction that `omega` resolves.

Notice that `omega` is doing something new here: in Level 1, it proved
a simple fact (`3 < 5`). Here, it **derives a contradiction** from two
hypotheses (`x.val = 5` and `x.val < 5`). `omega` reasons across all
hypotheses simultaneously — it sees everything in your context that
involves linear arithmetic over `ℕ` and `ℤ`, and either proves the
goal or finds a contradiction. This makes it your go-to tactic for
any arithmetic reasoning in this course.

This pattern — *extract the bound, derive a contradiction* — appears
whenever someone (or some proof branch) tries to use an out-of-range
value. The bound proof `.isLt` is the safety net that the type system
provides.

**Why does Fin start at 0?** You might wonder why `Fin 5` is
$\\{0,1,2,3,4\\}$ instead of $\\{1,2,3,4,5\\}$. The reason becomes
clear in the next world: the embedding `castSucc : Fin n -> Fin (n+1)`
preserves values exactly (`i.castSucc.val = i.val`), and `succ`
increments by exactly 1 (`i.succ.val = i.val + 1`). With 1-indexing,
these clean relationships would need offsets everywhere, making
every proof longer and harder to read.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
