import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 9

Title "Boss: A membership reasoning chain"

Introduction
"
# Boss: Integrating membership reasoning

Time to put together everything from this world. You will prove three
facts about `{1, 2, 3}` that exercise different membership techniques:

## Part A: Double absorption

Prove that `insert 1 (insert 3 {1, 2, 3}) = {1, 2, 3}`.

Both `1` and `3` are already in the finset, so inserting them does
nothing. You will use `Finset.insert_eq_of_mem` twice, each time
proving membership with `simp`.

## Part B: Membership containment

Prove that every element of `{1, 2, 3}` is also in `{0, 1, 2, 3, 4}`.

Given `x ∈ {1, 2, 3}`, you must case-split on `x` (using `rw [...] at h`
and `rcases`) to discover that `x` is 1, 2, or 3, then show each is
in the larger finset.

## Part C: Non-membership

Prove that `5 ∉ {1, 2, 3}`.

Use `simp` with membership lemmas to verify that 5 does not equal any
element.

## Strategy

Use `constructor` to split the conjunction into its three parts, then
tackle each part with the appropriate technique.
"

/-- Three membership facts about `{1, 2, 3}`: double idempotency,
containment in a larger finset, and non-membership of an outsider. -/
Statement :
    insert 1 (insert 3 ({1, 2, 3} : Finset Nat)) = {1, 2, 3} ∧
    (∀ x, x ∈ ({1, 2, 3} : Finset Nat) → x ∈ ({0, 1, 2, 3, 4} : Finset Nat)) ∧
    5 ∉ ({1, 2, 3} : Finset Nat) := by
  Hint "The goal is a conjunction of three parts. Start by splitting it."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · -- Part A: double idempotency
    Hint "**Part A**: You need to show that inserting 1 into
    `insert 3 (finset containing 1, 2, 3)` gives back the original finset.

    Both 1 and 3 are already in the finset, so both inserts are no-ops.
    Start with the outer `insert 1`: use `insert_eq_of_mem` to reduce
    the equality to a membership proof."
    Hint (hidden := true) "Use `rw [Finset.insert_eq_of_mem]`. This will
    create a side goal for the membership proof. Use
    `simp [Finset.mem_insert, Finset.mem_singleton]` for membership."
    rw [Finset.insert_eq_of_mem]
    · Hint "The outer insert is gone. Now handle the inner insert:
      `insert 3` of the finset. Same technique: `3` is already a member."
      Hint (hidden := true) "Use `rw [Finset.insert_eq_of_mem]` again,
      then prove membership with
      `simp [Finset.mem_insert, Finset.mem_singleton]`."
      rw [Finset.insert_eq_of_mem]
      simp [Finset.mem_insert, Finset.mem_singleton]
    · Hint "You need to show that `1` belongs to `insert 3` of the finset.
      Since 1 is in the original finset, it is certainly in the expanded
      one."
      Hint (hidden := true) "Use
      `simp [Finset.mem_insert, Finset.mem_singleton]`."
      simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Split the remaining conjunction."
    Hint (hidden := true) "Use `constructor`."
    constructor
    · -- Part B: membership containment
      Hint "**Part B**: Prove that every element of the smaller finset
      (containing 1, 2, 3) also belongs to the larger finset
      (containing 0, 1, 2, 3, 4).

      Start by introducing `x` and the membership hypothesis `hx`."
      Hint (hidden := true) "Use `intro x hx`."
      intro x hx
      Hint "You have `hx` saying `x` belongs to the finset containing
      1, 2, 3. To discover what `x` is, rewrite `hx` with `mem_insert`
      and case-split."
      Hint (hidden := true) "Use `rw [Finset.mem_insert] at hx` then
      `rcases hx with rfl | hx`."
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · Hint "In this case `x = 1`. Now show that `1` belongs to the
        larger finset."
        Hint (hidden := true) "Use
        `simp [Finset.mem_insert, Finset.mem_singleton]`."
        simp [Finset.mem_insert, Finset.mem_singleton]
      · Hint "Now `hx` says `x` belongs to `insert 2 (singleton 3)`.
        Peel another layer."
        Hint (hidden := true) "Use `rw [Finset.mem_insert] at hx`
        then `rcases hx with rfl | hx`."
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · Hint "In this case `x = 2`. Show that `2` belongs to the
          larger finset."
          Hint (hidden := true) "Use
          `simp [Finset.mem_insert, Finset.mem_singleton]`."
          simp [Finset.mem_insert, Finset.mem_singleton]
        · Hint "Now `hx` says `x` belongs to a singleton. Use
          `mem_singleton` to extract the equality."
          Hint (hidden := true) "Use `rw [Finset.mem_singleton] at hx`,
          then `rcases hx with rfl`, then
          `simp [Finset.mem_insert, Finset.mem_singleton]`."
          rw [Finset.mem_singleton] at hx
          rcases hx with rfl
          simp [Finset.mem_insert, Finset.mem_singleton]
    · -- Part C: non-membership
      Hint "**Part C**: Prove that `5` does not belong to the finset
      containing 1, 2, 3. This is a concrete non-membership fact."
      Hint (hidden := true) "Use
      `simp [Finset.mem_insert, Finset.mem_singleton]`."
      simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
Congratulations on completing the Membership world!

You proved three different kinds of membership reasoning:

**Part A** (absorption): You used `Finset.insert_eq_of_mem` to show
that inserting elements already present does nothing. Each application
reduced the goal to a membership proof, which `simp` handled.

**Part B** (containment by exhaustion): You used the `rw [...] at h` +
`rcases` pattern to case-split a variable membership into concrete
cases, then verified each case in the larger finset. This is the
finite-set analogue of proving a subset relation by checking each
element.

**Part C** (non-membership): You used `simp` to verify that 5 is not
equal to any element of {1, 2, 3}.

## What you learned in this world

- `Finset.mem_insert` -- the fundamental membership lemma (L01--L03)
- `Finset.mem_singleton` -- membership in singletons (L03)
- `simp [Finset.mem_insert, Finset.mem_singleton]` -- automated
  membership verification (L04--L05)
- `Finset.insert_eq_of_mem` -- inserting duplicates is absorbed (L06)
- Non-membership via `simp` (L07)
- `rw [...] at h` + `rcases` -- destructuring membership hypotheses
  for symbolic reasoning (L08, Boss)

## Transfer to paper proofs

These three patterns cover the core of finite-set membership reasoning
in ordinary mathematics:

- **Membership verification**: \"2 is in {1, 2, 3} because it is listed.\"
  In Lean, `simp` automates the scan.
- **Absorption**: \"Adding 2 to {1, 2, 3} does not change the set.\"
  In Lean, `insert_eq_of_mem` plus a membership proof.
- **Exhaustive case analysis**: \"If x is in {1, 2, 3}, then x is 1, 2,
  or 3.\" In Lean, `rw [mem_insert] at h` plus `rcases`.

## What comes next

In the next world, you will learn to reason about finset **union**,
**intersection**, and **difference**, and use the `ext` tactic to
prove finset equality by showing two finsets have the same members.
"

DisabledTactic trivial decide native_decide aesop simp_all
