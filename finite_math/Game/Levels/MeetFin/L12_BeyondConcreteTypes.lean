import Game.Metadata

World "MeetFin"
Level 12

Title "Beyond Concrete Types"

Introduction "
# From Fin 5 to Fin (n + 1)

Every level so far has used a *concrete* type — `Fin 5`, `Fin 3`,
`Fin 2`. But the techniques you've learned work for *any* `n`.

Here you'll prove something about `Fin (n + 1)` where `n` is an
arbitrary natural number. The element `x : Fin (n + 1)` has value
`x.val` and bound proof `x.isLt : x.val < n + 1`. The goal
`x.val ≤ n` follows from this bound.

The proof uses the same pattern as Level 3: extract the bound
with `have h := x.isLt`, then close with `omega`. The bound
`x.val < n + 1` implies `x.val ≤ n` — regardless of what `n` is.

(Note: `omega` is smart enough to find the bound automatically in
simple cases like this. But the explicit `have h := x.isLt` pattern
is important to learn — in more complex proofs, you'll need the
bound as a named hypothesis for rewriting, passing to other lemmas,
or chaining arithmetic steps.)

**Your task**: Prove that every element of `Fin (n + 1)` has value
at most `n`.
"

/-- Every element of `Fin (n + 1)` has value at most `n`. -/
Statement (n : ℕ) (x : Fin (n + 1)) : x.val ≤ n := by
  Hint "The bound is now a variable `n`, not a concrete number like 5.
  The constructor `⟨k, by omega⟩` won't work here because there's no
  specific number to plug in — but `.val` and `.isLt` still work the
  same way.

  Reminder: to construct a `Fin n` element when `n` is a variable,
  the pattern is `⟨k, by omega⟩` where the proof obligation is
  `k < n`. For extraction, `x.isLt` still gives `x.val < n + 1`."
  Hint "Extract the bound proof: `have h := x.isLt`. This gives
  `h : x.val < n + 1`."
  have h := x.isLt
  Hint "Now `{h}` says `x.val < n + 1`, which means `x.val ≤ n`.
  `omega` handles this conversion."
  omega

Conclusion "
The proof is identical to Level 3 — extract `.isLt`, close with
`omega`. The only difference is that `n` is a variable, not a
fixed number.

This demonstrates a key point: **all the techniques you've learned
generalize beyond concrete types**. Whether the type is `Fin 5`,
`Fin 100`, or `Fin (n + 1)` for an unknown `n`:
- `.val` extracts the number
- `.isLt` gives the bound proof
- `Fin.ext_iff` characterizes equality
- `omega` handles the arithmetic

In later worlds (starting with FinNavigation), you'll work with
variable `n` routinely. The moves are the same ones you've
practiced here.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
