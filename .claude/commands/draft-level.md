# /draft-level

Use when authoring one level.

## Prompt text

Design or write a single lean4game level around one dominant lesson.

You must explicitly state:
- the primary level type,
- the dominant lesson,
- the novelty budget,
- and why the statement shape is the right granularity.

Then design:
- intro/docstring,
- inventory behavior,
- docs for any new visible items,
- hint layers,
- any needed `Branch` usage,
- whether `Template` is justified,
- and the conclusion.

The level should teach a reusable move, not merely host a theorem.

Return exactly these sections:

1. Dominant lesson
2. Primary type
3. Novelty budget
4. Statement rationale
5. Docstring / intro rationale
6. Inventory behavior
7. Hint plan
8. Conclusion rationale
9. Likely failure states
10. Full code if code was requested
