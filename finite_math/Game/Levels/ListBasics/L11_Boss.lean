import GameServer.Commands
import Mathlib

World "ListBasics"
Level 11

Title "Boss: Map, filter, and membership"

Introduction
"
# Boss Level: Integrating list operations

Time to put together everything you have learned about lists.

You will prove a multi-step result that requires combining:
- **`List.mem_filter`** to unfold filter membership
- **`List.mem_map`** to unfold map membership
- **`refine`** to provide partial proofs
- **`constructor`** for conjunctions

## The statement

Given a list `l`, an element `a ∈ l`, and a predicate `p` such that
`p (f a) = true`, prove that `f a ∈ List.filter p (List.map f l)`.

In words: if `a` is in `l`, then `f a` is in the list obtained by first
mapping `f` and then filtering by `p` -- provided `p (f a)` is true.

## Planning the proof

Think about what `f a ∈ List.filter p (List.map f l)` means:
1. By `List.mem_filter`: `f a ∈ List.map f l ∧ p (f a) = true`
2. The second conjunct follows from `hp`
3. By `List.mem_map`: `∃ x ∈ l, f x = f a`
4. The witness is `a` itself, with `h` and `rfl`

There is no new material here -- only integration of skills from
Levels 3 through 6.
"

/-- If `a ∈ l` and `p (f a) = true`, then `f a ∈ List.filter p (List.map f l)`. -/
Statement (f : Nat → Nat) (p : Nat → Bool) (a : Nat) (l : List Nat)
    (h : a ∈ l) (hp : p (f a) = true) :
    f a ∈ List.filter p (List.map f l) := by
  Hint "The goal involves `List.filter` applied to `List.map`. Start
  by unfolding the filter membership. Try `rw [List.mem_filter]`."
  rw [List.mem_filter]
  Hint "The goal is now `f a ∈ List.map f l ∧ p (f a) = true`. Split
  it with `constructor`."
  constructor
  · Hint "The goal is `f a ∈ List.map f l`. This is the membership-preservation
    property of `map`. Unfold it with `rw [List.mem_map]`."
    rw [List.mem_map]
    Hint "The goal is `∃ a_1 ∈ l, f a_1 = f a`. Provide the witness `a`
    together with the membership proof `h`, leaving only the equality.
    Try `refine ⟨a, h, ?_⟩`."
    refine ⟨a, h, ?_⟩
    Hint "The goal is `f a = f a`. Try `rfl`."
    rfl
  · Hint "The goal is `p (f a) = true`. This is hypothesis `hp`. Try `exact hp`."
    exact hp

DisabledTactic decide native_decide simp aesop

Conclusion
"
Congratulations on completing the Lists world!

You proved that mapping and then filtering preserves membership (for
elements satisfying the predicate). This required decomposing the problem
into layers:

1. **Filter layer**: `f a ∈ List.filter p (List.map f l)` means
   `f a ∈ List.map f l` **and** `p (f a) = true`
2. **Map layer**: `f a ∈ List.map f l` means there exists some `x ∈ l`
   with `f x = f a`
3. **Witness**: the element `a` itself, with `h : a ∈ l` and `rfl`
4. **Predicate**: `p (f a) = true` from hypothesis `hp`

Each layer used a lemma you learned earlier in this world. The boss
integrates them into a single coherent proof.

## What you learned in this world

1. **List constructors**: `[]` is the empty list, `a :: l` prepends `a` to `l`,
   and `[a, b, c]` is sugar for `a :: b :: c :: []`
2. **`List.length`**: counts the number of elements. `List.length_cons`
   unfolds it on a cons cell.
3. **`List.Mem`** (written `∈`): membership defined recursively.
   `List.mem_cons` unfolds it into `a = b ∨ a ∈ l`.
4. **`List.append`** (written `++`): concatenation. `List.mem_append`
   characterizes membership. `List.length_append` gives the length.
5. **`List.map f l`**: applies `f` to every element. `List.mem_map`
   characterizes membership via an existential witness.
6. **`List.filter p l`**: keeps elements satisfying `p`. `List.mem_filter`
   characterizes membership via a conjunction.
7. **`List.get`**: accesses elements by `Fin`-indexed position.
8. **`List.Nodup`**: no duplicate elements. `List.nodup_cons` unfolds it.

## Transfer to paper proofs

The proof you just wrote says:

\"To show $f(a)$ is in the filtered mapped list, we need two things:
that $f(a)$ is in the mapped list (which holds because $a$ is in the
original list, so $f(a)$ is the image of an element we started with),
and that $p(f(a))$ is true (which is given).\"

Each tactic step corresponds to a sentence in this argument.

## What comes next

In the next world, you will learn about **multisets** -- what happens
when you keep the multiplicities but forget the ordering. The `Nodup`
property you learned in Level 9 is the bridge: a list satisfying `Nodup`
gives rise to a finset without losing information about which elements
are present. The journey from lists to multisets to finsets is the central
structural story of this course.

**Permutations preview**: Two lists that contain the same elements in a
different order are called *permutations* of each other. In the next world,
`List.Perm` formalizes this, and you will see that two lists that are
permutations give rise to the same multiset.
"
