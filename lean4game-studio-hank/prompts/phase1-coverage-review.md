# Coverage Review

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `{course}/coverage-map.md` — the coverage map to review
3. `long_term.md` — the course description and scope

## Your job

Verify the coverage map is complete and accurate. This is NOT a review of content (no content exists yet). This is a review of the PLAN for what to cover.

## What to check

### 1. Scope completeness

Read the course description in `long_term.md`. For every topic, definition, and theorem family mentioned, verify it appears in the coverage map. If something is mentioned in `long_term.md` but missing from the map, that is a P0 defect.

### 2. Mathlib verification

Use WebSearch and WebFetch to check the current mathlib documentation for the topics in this course. Verify:
- Do the API names in the coverage map match current mathlib? (Names change between versions.)
- Are there important mathlib definitions or theorem families in this area that the coverage map missed?
- Search `https://leanprover-community.github.io/mathlib4_docs/` for the relevant modules.

### 3. Proof-move clusters

Are the proof-move clusters realistic? Do they actually correspond to how proofs in this area work? Are there common proof patterns the map missed?

### 4. Example plan

Does every major definition have at least one planned concrete example? Are counterexamples planned for important theorems?

### 5. Exploit awareness

Does the map identify the key exploit vectors (automation tactics, library lemmas, lattice aliases) that will need to be disabled?

## Output

Write your output to `{course}/reviews/coverage-review-current.md`.

Format:
1. **Scope gaps** — topics from `long_term.md` missing from the map (P0 if core topic)
2. **Mathlib discrepancies** — API names that don't match current mathlib, missing mathlib content
3. **Proof-move gaps** — missing or unrealistic proof-move clusters
4. **Example gaps** — definitions without planned examples
5. **Exploit gaps** — missing exploit vectors
6. **Overall verdict** — PASS or FAIL
