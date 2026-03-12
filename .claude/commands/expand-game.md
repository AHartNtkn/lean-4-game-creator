# /expand-game

Use when adding new material to an existing game.

## Prompt text

Expand this lean4game repo without breaking its house style or its coverage logic.

First:
1. infer local style,
2. map current coverage,
3. identify the coverage gap the new material should close,
4. decide the correct insertion point,
5. and only then draft the new content.

Your output must include:
- what the new material covers,
- what proof moves it teaches,
- how its granularity fits the existing course,
- how dependencies change,
- what inventory changes are required,
- and what must be re-playtested because of the seam.

Return exactly these sections:

1. Style constraints to preserve
2. Current coverage gap
3. Insertion point and rationale
4. New world or level plan
5. Dependency changes
6. Inventory and doc changes
7. Boss / transfer implications
8. Regression risks
9. Full code if code was requested
10. Post-expansion playtest plan
