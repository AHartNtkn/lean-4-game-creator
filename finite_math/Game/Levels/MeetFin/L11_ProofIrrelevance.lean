import Game.Metadata

World "MeetFin"
Level 11

Title "Only the Value Matters"

Introduction "
# Proof Irrelevance for Fin

A `Fin n` element bundles a value with a *proof* that the value is
in range. But what if two elements have the same value? Are they
the same element?

The answer: **only the value matters**. Two `Fin` elements with the
same underlying natural number are equal, regardless of how their
bound proofs were obtained. This follows directly from `Fin.ext_iff`:
equality depends only on `.val`.

Here you have two elements `a` and `b` of `Fin 5`, and you know
`ha : a.val = 3` and `hb : b.val = 3`. Since both have value `3`,
they must be equal.

In practice, you might get bound proofs from different sources —
one from a hypothesis, one from `omega`, one from a lemma. Proof
irrelevance means you never need to worry about *which* proof was
used.

**Strategy**: Use `rw [Fin.ext_iff]` to reduce to a value equality,
then use `omega` to close the arithmetic (since `ha` and `hb`
together imply `a.val = b.val`).
"

/-- Fin elements with the same value are equal, regardless of the bound proof. -/
Statement (a b : Fin 5) (ha : a.val = 3) (hb : b.val = 3) : a = b := by
  Hint "Use `rw [Fin.ext_iff]` to reduce the `Fin` equality to a
  value equality."
  rw [Fin.ext_iff]
  Hint "Now the goal is `a.val = b.val`. You know `{ha}` and
  `{hb}` — both values are `3`. `omega` can close this."
  omega

Conclusion "
This property is called **proof irrelevance**: the identity of a
`Fin` element depends only on its value, not on which proof
witnesses the bound. This is a direct consequence of the eta
principle (`Fin.eta` / `Subtype.eta` from Levels 9–10): since an
element is determined by its value, two elements with the same
value must be equal — regardless of how their bound proofs were
obtained.

Notice the proof pattern: `rw [Fin.ext_iff]` then `omega`. This
two-step combo — **reduce to values, then compute** — is the
standard way to prove `Fin` equalities when the values can be
determined from hypotheses. We'll call this the **Fin equality
pattern**: `rw [Fin.ext_iff]; omega`. You'll use it frequently.

The deeper reason this works is that **`Prop` is proof-irrelevant
in Lean**: any two proofs of the same proposition are considered
equal. So `hv1 : k < n` and `hv2 : k < n` — no matter how they
were obtained — are the same proof. This means `⟨k, hv1⟩ = ⟨k, hv2⟩`
automatically, and equality of `Fin` elements reduces to equality
of values.

This isn't special to `Fin` — it applies to **every subtype** in Lean.
Any type of the form `{ x : α // P x }` (a value bundled with a
proof) has the same property: two elements are equal when their values
are equal, regardless of the proofs. The same `ext_iff + omega`
pattern works for any subtype where the predicate involves arithmetic.
You'll meet other subtypes later (like `{ n : ℕ // n.Prime }`), and
proof irrelevance will apply there too.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
