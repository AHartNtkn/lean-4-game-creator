# /coverage-map

Use when planning or auditing a course, world, or world sequence.

## Prompt text

Build a coverage and granularity map for this lean4game content.

Track coverage across these axes:
- MATH
- MOVE
- LEAN
- NOTATION
- MISCONCEPTION
- TRANSFER

For each core item, record:
- importance
- first introduction
- supported practice
- unsupported retrieval
- integration
- transfer
- warning / misconception handling

Then analyze granularity at:
- course scale
- world scale
- level scale

Also produce:
- novelty hotspots
- weak closure items
- uncovered items
- redundant items
- recommended splits or merges
- recommended new bridge levels

Do not stop at theorem coverage. I care at least as much about proof-move coverage and notation / misconception coverage.

Return exactly these sections:

1. Coverage matrix summary
2. Core uncovered items
3. Weakly covered items
4. Redundant items
5. Granularity defects
6. Novelty hotspots
7. Recommended splits or merges
8. Suggested new levels or worlds
9. Inventory items that should be delayed, hidden, or better documented
10. Confidence notes
