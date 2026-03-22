import Game.Metadata

World "AbstractionLadder"
Level 5

Title "Duplicate Elements"

Introduction "
# Lists Can Have Duplicates

Before we move to permutations, let's observe something important:
**lists can contain duplicate elements**.

Consider a list `l` where element `a` already appears (`a ∈ l`).
If you prepend `a` to `l` with `a :: l`, the resulting list has
`a` appearing at least twice — once at the head, and at least once
in the tail.

This is a preview of the abstraction ladder:

| Layer | Duplicates? | Count measure |
|---|---|---|
| **List** | yes | `.length` counts all entries |
| **Multiset** | yes | `.card` counts all entries |
| **Finset** | no | `.card` counts distinct elements |

Lists and multisets keep every copy. Finsets discard duplicates,
so their `.card` can be strictly smaller than the list `.length`.

**Your task**: Given a list `l` of length 1 and an element `a`
that belongs to `l`, compute the length of `a :: b :: l`.

Since `a ∈ l`, the list `a :: b :: l` contains `a` at least twice.
But `.length` counts all entries — duplicates included. You'll peel
off each `cons` with `List.length_cons` and close with the hypothesis.
"

/-- Prepending two elements to a list increases its length by 2. -/
Statement (a b : ℕ) (l : List ℕ) (hmem : a ∈ l) (hlen : l.length = 1) :
    (a :: b :: l).length = 3 := by
  Hint "The outermost structure is `a :: (b :: l)`. Use
  `rw [List.length_cons]` to peel off `a`."
  rw [List.length_cons]
  Hint "Good! The goal is now `(b :: l).length + 1 = 3`. Peel off
  `b` with another `List.length_cons`."
  rw [List.length_cons]
  Hint "The goal is now `l.length + 1 + 1 = 3`. Use the hypothesis
  `hlen : l.length = 1` to substitute."
  Hint (hidden := true) "Try `rw [hlen]`."
  rw [hlen]

Conclusion "
You computed the length by peeling off each `cons` with
`List.length_cons`, then closing with the known tail length.

The pattern:
```
(a :: b :: l).length = (b :: l).length + 1    (length_cons)
                     = l.length + 1 + 1        (length_cons)
                     = 1 + 1 + 1               (hypothesis)
                     = 3
```

The hypothesis `hmem : a ∈ l` wasn't needed for the length
calculation — `.length` counts all entries regardless of duplicates.
But it matters *conceptually*: the list `a :: b :: l` contains `a`
at least twice (once at the head, once in `l`). This means:
- As a **list**: `.length = 3` (counts everything)
- As a **finset**: `.card` could be 2 or 3 (depending on `b`)

Later in this world, you'll see exactly how the nodup condition
determines whether card equals length.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
