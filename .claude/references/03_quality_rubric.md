# Quality rubric

Use this rubric to grade a level, a world, or a whole game.

Score each category from 0 to 4.

- **4** excellent
- **3** solid
- **2** needs revision
- **1** serious problem
- **0** absent or broken

A result should not be called “good” unless:
- the average is at least 3,
- no category is below 2,
- and none of the automatic red flags apply.

## 1. Coverage closure

Questions:
- Are the important concepts and proof moves explicitly tracked?
- Does each high-value item appear in introduction, supported use, retrieval, integration, and transfer where appropriate?
- Are there hidden prerequisite gaps?

A 4 means the coverage map is explicit and convincing.  
A 1 means the content contains major uncovered moves.  
A 0 means the author is guessing.

## 2. Granularity fit

Questions:
- Is each level scoped to one dominant lesson?
- Is each world centered on a coherent theorem family or proof pattern?
- Are levels too broad or too trivial?

A 4 means the cuts feel inevitable.  
A 1 means levels fail for many unrelated reasons or teach nothing reusable.

## 3. Proof-move teaching

Questions:
- Does the content teach how to proceed, not only what theorem is true?
- Are proof shapes, witness choices, contradiction setups, definition unfolding, and similar moves made visible?
- Can a learner generalize the method?

A 4 means the game clearly teaches proof habits.  
A 1 means the game is theorem trivia plus syntax.

## 4. Inventory design

Questions:
- Are tactics/theorems/definitions unlocked at the right time?
- Is the visible inventory coherent and uncluttered?
- Are theorem tabs and hidden aliases used well?
- Are new items documented properly?

A 4 means the inventory feels like a carefully edited syllabus.  
A 1 means it feels like a junk drawer.

## 5. Hint design and recoverability

Questions:
- Do hints trigger in the right contexts?
- Do they rescue without replacing thought?
- Are common dead ends covered?
- Are there layered hints where needed?

A 4 means stuck learners recover intelligently.  
A 1 means hints are mistimed, absent, or spoilery.

## 6. Worked example -> practice -> transfer -> boss

Questions:
- Does the sequence move from demonstration to independence?
- Is support faded rather than dropped?
- Does the boss integrate the world’s repertoire?
- Do psets force transfer under a new surface form?

A 4 means progression is deliberate and visible.  
A 1 means the course either hand-holds forever or drops learners abruptly.

## 7. Mathematical authenticity

Questions:
- Are the mathematical stakes and ideas clear?
- Do intros and conclusions explain why the material matters?
- Are warnings and intuitions mathematically honest?

A 4 means the learner feels they are learning mathematics, not arbitrary software rituals.  
A 1 means the course is mechanically correct but conceptually empty.

## 8. Paper-proof transfer

Questions:
- Do explanations connect Lean moves to ordinary proof language?
- Are proofs broken into subgoals in a way that helps later written proof?
- Are syntax choices and docstrings helping, not hurting, transfer?

A 4 means the course improves non-Lean proof skill.  
A 1 means it creates brittle command memorization.

## 9. Technical fit and maintainability

Questions:
- Does the content compile and run cleanly?
- Are dependencies sane?
- Does each world maintain a coherent center of gravity?
- Is the repo easy to extend without style drift?

A 4 means the technical layer supports the curriculum.  
A 1 means the technical layer is undermining it.

## Automatic red flags

Any of the following should block a “good” verdict until fixed:

- a boss that depends on an untaught micro-skill
- a world that mixes unrelated theorem families or whose intro cannot coherently explain its purpose
- missing docs for newly unlocked high-value inventory items
- hints that do not match the actual failure states
- psets that merely clone lecture examples
- a level that introduces too many new burdens at once
- unresolved local-run or publish breakage
- issue reports revealing learner confusion that the course still ignores
