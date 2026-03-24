import Game.Metadata

World "PreimageWorld"
Level 3

Title "Preimage with a Non-Injective Function"

TheoremTab "Set"

Introduction "
# When Multiple Inputs Map to the Same Output

In the last two levels, you used `n ↦ n + 1`, which maps each
input to a unique output (it is **injective**). But preimage is
most interesting with **non-injective** functions — functions where
multiple inputs can map to the same output.

Consider the constant function `fun _ : ℕ => 7` — it maps EVERY
natural number to 7, regardless of the input. What is the preimage
of `{m | m < 10}` under this function?

Since every input maps to 7, and `7 < 10`, EVERY natural number
is in the preimage. Both 0 and 1000 qualify — for the same reason.

**Your task**: Prove that both 0 and 1000 are in the preimage of
`{m | m < 10}` under the constant function `fun _ => 7`.

**Proof plan**:
1. `constructor` — split the `∧`
2. Each part: `show 7 < 10` then `omega`

Notice that the two proofs will be **identical** — the input
doesn't matter at all.
"

/-- Both 0 and 1000 are in the preimage because the function always outputs 7, and 7 < 10. -/
Statement : (0 : ℕ) ∈ (fun _ : ℕ => (7 : ℕ)) ⁻¹' {m | m < 10} ∧
            (1000 : ℕ) ∈ (fun _ : ℕ => (7 : ℕ)) ⁻¹' {m | m < 10} := by
  Hint "Use `constructor` to split the conjunction into two goals."
  constructor
  · Hint "The goal says `0 ∈ (fun _ => 7) ⁻¹' ...`. By preimage
    membership, this means `(fun _ => 7) 0 ∈ ...`, which is `7 < 10`.
    Use `show 7 < 10` to make this explicit."
    Hint (hidden := true) "`show 7 < 10` then `omega`."
    show 7 < 10
    omega
  · Hint "Same thing for 1000: `(fun _ => 7) 1000 = 7`, so the
    goal is again `7 < 10`."
    Hint (hidden := true) "`show 7 < 10` then `omega`."
    show 7 < 10
    omega

Conclusion "
Both proofs were identical: `show 7 < 10` then `omega`. The input
(0 or 1000) never appeared in the proof because the constant
function ignores its input entirely.

**The preimage \"expands\" inputs**: For the injective function
`n ↦ n + 1`, each output comes from exactly one input, so the
preimage of a set \"looks like\" the original set. But for a
non-injective function like `_ ↦ 7`, a single output value can
come from infinitely many inputs. The preimage of any set
containing 7 is ALL of `ℕ`.

This is why preimage is fundamentally different from function
inversion. An inverse function (when it exists) maps each output
to one input. Preimage maps each output to the set of ALL inputs
that produce it — which can be empty, finite, or infinite.

**Foreshadowing**: In Injective World, you will prove that
`f ⁻¹' (f '' s) = s` for all `s` implies `f` is injective.
The constant function shows why this can fail: `f '' {0} = {7}`,
so `f ⁻¹' (f '' {0}) = f ⁻¹' {7} = ℕ ≠ {0}`.

**Looking ahead in this world**: In Level 14, you will discover
the deeper reason preimage is so well-behaved: it is just function
composition on predicates. The non-injectivity you saw here — many
inputs mapping to one output — is exactly what makes image harder
than preimage. Preimage does not care about multiple preimages;
it simply composes and checks. Injectivity matters for image, not
for preimage.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
