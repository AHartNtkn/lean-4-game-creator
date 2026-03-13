import Game.Metadata

World "GroupTutorial"
Level 6

Title "calc Blocks"

Introduction
"
When proofs have multiple rewrite steps, a `calc` block forces you to
state what each step achieves before justifying it. This is how paper
proofs work: you say \"this equals that by such-and-such.\"

```
calc expression₁
    _ = expression₂ := by rw [lemma₁]
    _ = expression₃ := by rw [lemma₂]
    _ = expression₄ := by rw [lemma₃]
```

Each line starts with `_ =` and ends with `:= by` followed by the
justification. The `_` stands for \"the result of the previous step.\"

In this level, the parentheses need to move the **other** way compared
to Level 5. In Level 5, `rw [mul_assoc]` moved parentheses rightward.
To go leftward — from `a * (b * c)` to `(a * b) * c` — write
`rw [← mul_assoc]`. The `←` (typed `\\l` or `\\left`) reverses the
rewrite direction.

**Your task**: prove `a⁻¹ * (a * b) = b` using a `calc` block.
"

/-- The `calc` tactic lets you write a chain of equalities step by step.

```
calc expression₁
    _ = expression₂ := by rw [lemma₁]
    _ = expression₃ := by rw [lemma₂]
```

Each step must be justified. A `calc` block forces you to plan each
intermediate result, which is close to how you would write a proof on
paper.

**Common syntax errors**: make sure each step starts with `_ =` (with
spaces), ends with `:= by`, and is indented consistently. -/
TacticDoc «calc»

NewTactic «calc»

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  Hint "This is the same re-bracket / cancel / clean up pattern from
  Level 5, but the parentheses need to move **leftward**.

  Plan your three steps:
  1. Re-bracket leftward using `← mul_assoc`
  2. Cancel `a⁻¹ * a` using `inv_mul_cancel`
  3. Clean up with `one_mul`

  Write this as a `calc` block. Start with `calc a⁻¹ * (a * b)` and
  then write each `_ = ...` step."
  Hint (hidden := true) "A `calc` block looks like this:
  ```
  calc a⁻¹ * (a * b)
      _ = (a⁻¹ * a) * b := by rw [← mul_assoc]
      _ = ...            := by ...
      _ = ...            := by ...
  ```
  Fill in the last two steps."
  Branch
    -- Plain rw chain (also accepted)
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  Branch
    rw [← mul_assoc]
    rw [inv_mul_cancel]
    rw [one_mul]
  calc a⁻¹ * (a * b)
      _ = (a⁻¹ * a) * b := by rw [← mul_assoc]
      _ = 1 * b          := by rw [inv_mul_cancel]
      _ = b              := by rw [one_mul]

Conclusion
"
The `calc` block forces you to state each intermediate expression.
This is close to how you would write a proof on paper: \"by associativity,
this equals ... by the inverse law, this equals ...\"

Compare:

**rw chain**: `rw [← mul_assoc, inv_mul_cancel, one_mul]`

**calc block**: shows what each step achieves.

Both are valid. For short proofs, `rw` chains are fine. For longer
proofs, `calc` blocks help you plan and track the proof.

Notice that `← mul_assoc` moved parentheses **leftward**: from
`a⁻¹ * (a * b)` to `(a⁻¹ * a) * b`. Remember:
- `rw [mul_assoc]` moves parentheses right: `(x * y) * z → x * (y * z)`
- `rw [← mul_assoc]` moves parentheses left: `x * (y * z) → (x * y) * z`
"
