import Game.Metadata

World "Finale"
Level 15

Title "The Infinite Counterexample"

Introduction "
# When Finiteness Fails

You just proved that every injective endofunction on `Fin n`
is surjective. But this is deeply tied to **finiteness** — the
cardinality sandwich that powers the proof has no meaning for
infinite types.

**Counterexample**: The successor function $f(n) = n + 1$ on
$\\mathbb{N}$ is injective ($a + 1 = b + 1 \\implies a = b$)
but NOT surjective ($0$ has no preimage).

Prove both halves of this conjunction:
1. **Injective**: if $a + 1 = b + 1$, then $a = b$ (arithmetic)
2. **Not surjective**: show that $0$ has no preimage, since
   $x + 1 \\ge 1 > 0$ for every natural number $x$
"

/-- The successor function on ℕ is injective but not surjective. -/
Statement : Function.Injective (fun n : ℕ => n + 1) ∧
    ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  -- Part 1: Injective
  Hint "Split the conjunction into two goals."
  Hint (hidden := true) "Try `constructor`."
  constructor
  · Hint "Prove injectivity: if `f a = f b`, then `a = b`.
    Introduce `a`, `b`, and the equality hypothesis."
    Hint (hidden := true) "Try `intro a b hab`."
    intro a b hab
    Hint "The hypothesis `hab` says `(fun n => n + 1) a = (fun n => n + 1) b`.
    Extract the arithmetic form `a + 1 = b + 1` so `omega` can use it."
    Hint (hidden := true) "Try `have h : a + 1 = b + 1 := hab` then `omega`."
    have h : a + 1 = b + 1 := hab
    omega
  -- Part 2: Not surjective
  · Hint "Prove non-surjectivity: assume `f` is surjective and
    derive a contradiction. Which element of `ℕ` has no preimage
    under the successor function?"
    Hint (hidden := true) "Try `intro hsurj`."
    intro hsurj
    Hint "Apply the surjectivity hypothesis to `0` — the element
    with no preimage — to get a supposed preimage."
    Hint (hidden := true) "Try `obtain ⟨x, hx⟩ := hsurj 0`."
    obtain ⟨x, hx⟩ := hsurj 0
    Hint "`hx` says `(fun n => n + 1) x = 0`. Extract the
    arithmetic form `x + 1 = 0`, which is impossible for
    natural numbers."
    Hint (hidden := true) "Try `have h : x + 1 = 0 := hx` then `omega`."
    have h : x + 1 = 0 := hx
    omega

Conclusion "
**The infinite counterexample**: $f(n) = n + 1$ on $\\mathbb{N}$
is injective but not surjective.

| Half | Key step | Why it works |
|------|----------|-------------|
| Injective | `omega` | $a + 1 = b + 1 \\implies a = b$ |
| Not surjective | `obtain` + `omega` | $x + 1 = 0$ is impossible for $x : \\mathbb{N}$ |

**Why this matters**: The boss proof relied on the
**cardinality sandwich** — $n$ distinct elements in an
$n$-element set must cover everything. For $\\mathbb{N}$,
infinitely many distinct elements still leave room for gaps.
The cardinality sandwich has no analogue when 'same size' loses
its meaning.

This contrast is one of the deepest lessons of the course:
finiteness is not a technicality but a structural property that
enables counting arguments.

**The endofunction hypothesis matters too**: Finiteness alone
is not enough — the function must also be an **endofunction**
(same domain and codomain). `Fin.castSucc : Fin n -> Fin (n + 1)`
is injective but not surjective, even though both types are
finite. The boss theorem requires `f : Fin n -> Fin n` — the
cardinality sandwich only works when the domain and codomain
have the same size.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
