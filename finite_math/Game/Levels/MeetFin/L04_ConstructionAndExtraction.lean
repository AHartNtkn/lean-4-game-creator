import Game.Metadata

World "MeetFin"
Level 4

Title "Combining Bounds"

Introduction "
# Two Elements, Two Bounds

In Level 3, you extracted a single bound with `.isLt` and used `omega`.
Here you'll combine bounds from **two** elements.

Every `Fin 5` element has value less than 5. So if `i` and `j` are
both in `Fin 5`, their values satisfy `i.val < 5` and `j.val < 5`.
What can you conclude about their sum?

Since `i.val ≤ 4` and `j.val ≤ 4`, the sum `i.val + j.val ≤ 8`.

**Strategy**: Extract both bound proofs with `have`, then let `omega`
chain them together.

Step by step:
1. `have h1 := i.isLt` — gives `h1 : i.val < 5`
2. `have h2 := j.isLt` — gives `h2 : j.val < 5`
3. `omega` — deduces `i.val + j.val ≤ 8` from both bounds
"

/-- The sum of two Fin 5 values is at most 8. -/
Statement (i j : Fin 5) : i.val + j.val ≤ 8 := by
  Hint "Extract the first bound: `have h1 := i.isLt`."
  have h1 := i.isLt
  Hint "Extract the second bound: `have h2 := j.isLt`."
  have h2 := j.isLt
  Hint "Now `{h1}` says `i.val < 5` and `{h2}` says `j.val < 5`.
  `omega` combines these to prove `i.val + j.val ≤ 8`."
  omega

Conclusion "
You combined two `.isLt` bounds and let `omega` chain them.

This demonstrates a key principle: **every `Fin n` element carries
useful information** in its bound proof. When you have multiple
`Fin` elements, their bounds combine to constrain their values.

The pattern generalizes:
- One element: `have h := i.isLt; omega`
- Two elements: extract both bounds, then `omega`
- $k$ elements: extract all bounds, then `omega`

`omega` reasons across ALL hypotheses simultaneously — you just need
to make the bounds visible by extracting them with `have`.

*Shortcut you'll appreciate later*: In many cases, `omega` can find
`.isLt` bounds automatically without explicit `have` lines — it sees
all hypotheses in your context, including the implicit bound proofs
that Lean tracks for `Fin` elements. The explicit `have h := x.isLt`
pattern taught here is still valuable for clarity and for passing
bounds to other lemmas, but don't be surprised if `omega` sometimes
closes a goal without being told about the bounds first.

The `⟨value, proof⟩` constructor (Level 1) and the `.val` / `.isLt`
extractors (Levels 2–3) form a complete round-trip: you can take a
`Fin` element apart and put it back together. You'll see this
round-trip formalized starting in Level 5.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
