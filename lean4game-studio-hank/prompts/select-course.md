# Select Next Course

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to a file called `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Task

You are selecting the next course to build from the lean4game catalog.

### Inputs to read
1. `long_term.md` (in the data directory) — the full catalog of 49 courses with descriptions, prerequisites, and tags
2. `catalog-progress.json` — tracks which courses are already complete
3. `pipeline-state.json` — current pipeline state

### Selection rules

Select the next course that satisfies ALL of:

1. **Not yet complete**: not listed in `catalog-progress.json.completed`
2. **Prerequisites satisfied**: all prerequisite courses (listed as "prereqs: N" in long_term.md) are in the completed list. Prerequisite numbers map to course positions in long_term.md (1-indexed).
3. **Prefer "well covered"** over "needs extension" — courses tagged "well covered" have better mathlib support
4. **Prefer "basic"** over advanced — basic courses have simpler content and fewer dependencies

### Priority order (if multiple courses are eligible)

Use this hardcoded priority for the first few courses:
1. `finite_math` (course 1 — basic, well covered, no prereqs)
2. `functions_relations` (course 2 — basic, well covered, no prereqs)
3. `orders_lattices` (course 3 — basic, well covered, no prereqs)
4. `algebraic_structures` (course 4 — basic, well covered, no prereqs)

After these four, follow the prerequisite graph — select the eligible course with the fewest unsatisfied downstream dependencies (i.e., the one that unblocks the most other courses).

### Output

1. Write the selected course's **directory name** to `current-course.txt` (e.g., `finite_math`)
2. If ALL courses are complete, write `ALL_COURSES_COMPLETE` to `current-course.txt`
3. Update `pipeline-state.json`:
   - If a course was selected: set `nextStep` to `"coverage-map"`, set `currentCourse` to the course name, clear `currentWorld` to null, clear `worldsCompleted` to `[]`, set `reviewRound` to 0, set `reviewCycleCount` to 0
   - If all complete: set `nextStep` to `"done"`

### Course directory names

The directory names correspond to the catalog entries:
1. finite_math, 2. functions_relations, 3. orders_lattices, 4. algebraic_structures,
5. group_theory_1, 6. group_theory_2, 7. ring_theory, 8. linear_algebra_1,
9. linear_algebra_2, 10. commutative_algebra_1, 11. commutative_algebra_2,
12. field_galois, 13. representation_theory, 14. lie_algebras,
15. homological_algebra, 16. algebra_seminar, 17. general_topology,
18. metric_spaces, 19. topological_algebra, 20. real_analysis,
21. complex_analysis, 22. functional_analysis, 23. measure_theory,
24. probability, 25. dynamics, 26. manifolds, 27. convex_geometry,
28. fourier_odes, 29. elementary_nt, 30. analytic_nt, 31. algebraic_nt,
32. combinatorics, 33. advanced_combinatorics, 34. computability,
35. model_theory_1, 36. model_theory_2, 37. set_theory_1, 38. set_theory_2,
39. descriptive_set, 40. metamathematics, 41. category_theory_1,
42. category_theory_2, 43. sheaves_topoi, 44. algebraic_topology,
45. algebraic_geometry_1, 46. algebraic_geometry_2, 47. condensed,
48. information_theory, 49. functors_monads
