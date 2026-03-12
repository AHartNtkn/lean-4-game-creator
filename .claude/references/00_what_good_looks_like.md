# What good lean4game authorship looks like

A person who is genuinely good at creating lean4game courses is not someone who has memorized all the commands.

A genuinely good author can do all of the following:

## 1. Decompose mathematics into teachable proof moves

A textbook chapter is too coarse. A theorem statement is too coarse. A lean4game author must be able to see that a result actually depends on smaller things such as:

- unfolding a definition,
- introducing quantifiers,
- choosing a witness,
- specializing a hypothesis,
- rewriting in the right direction,
- normalizing an algebraic expression,
- extracting structure from a conjunction or existential,
- setting up contradiction or contraposition,
- choosing the right auxiliary lemma,
- spotting when a sequence, bound, or subsequence construction is the real move.

The game should teach those moves explicitly.

## 2. Track coverage on multiple axes

A good course does not merely cover theorems. It tracks coverage across at least six axes:

- **mathematical objects and definitions**
- **theorem families**
- **proof strategies and proof shapes**
- **Lean tactics / commands / syntax**
- **notation and coercions**
- **misconceptions and failure modes**

If an item matters, the course should know where it is first introduced, where it is practiced with scaffolding, where it is retrieved without scaffolding, where it is integrated into a larger proof, and where it is transferred to a fresh setting.

## 3. Choose good granularity

A level should usually have one dominant lesson.

That lesson can be:
- a new tactic,
- a new definition,
- a new proof pattern,
- a subtle notation issue,
- a warning about a common false move,
- or an integration task.

A level is too broad if a learner can fail for five unrelated reasons.  
A level is too fine if solving it teaches nothing reusable.

A world should feel like a chapter with a center of gravity. By the end of the world, a learner should be able to say:
- what family of ideas it covered,
- what new moves they learned,
- and what the boss asked them to integrate.

## 4. Teach the how over the what

In a lean4game course, the theorem statement is the surface. The proof process is the substance.

The right question is not merely:
- “Did the player prove theorem T?”

The right questions are:
- “Did the player learn to unpack this kind of definition?”
- “Did they learn when to use `intro`, `use`, `specialize`, `change`, `have`, or contradiction?”
- “Can they recognize the proof shape when the surface theorem changes?”
- “Can they explain in plain language what their proof is doing?”

## 5. Use scaffold fade, not scaffold drop

A good author stages support:

- first contact: heavy explanation, explicit docs, rescue hints
- second contact: partial prompting
- third contact: transfer problem with little or no prompting
- boss: integration with minimal hand-holding
- later pset/review: retrieval under a new surface form

The goal is not permanent support. The goal is durable independence.

## 6. Write intros and conclusions that do real work

Good intros do one of the following:
- motivate a definition,
- explain why the next result matters,
- give the geometric or historical picture,
- tell the learner what proof shape to expect,
- warn about a tempting false move.

Good conclusions do one of the following:
- compress the proof into a reusable recipe,
- translate the Lean proof into ordinary mathematical language,
- explain what to notice next time,
- connect the level to the wider theorem family.

Empty congratulations are weak. Consolidation is strong.

## 7. Treat inventory design as curriculum design

The inventory is not a toolbox dump. It is the visible syllabus.

A new inventory item should appear only when at least one of these is true:
- the level is teaching the item directly,
- the item is now a stable part of the learner’s repertoire,
- the item is needed for transfer or integration.

Good authors hide aliases and low-level variants when that improves usability and clarity. They also keep theorem tabs, docs, and naming coherent so the inventory reduces search burden rather than increasing it.

## 8. Build bosses that integrate, not merely repeat

A boss should:
- require several moves learned in the world,
- feel recognizably “about” the world,
- reward synthesis,
- expose weak spots in understanding,
- and produce a meaningful sense of consolidation.

A boss is bad when it is:
- just longer than the earlier levels,
- a single algebra grind,
- solved by replaying one example,
- or dependent on a trick that was never isolated beforehand.

## 9. Design for paper-proof transfer

The best lean4game courses improve ordinary proof writing. That means they should help learners:
- break proofs into subgoals,
- understand the role of quantifiers and witnesses,
- articulate proof strategy in words,
- and connect Lean steps to mathematical reasoning.

If the course creates button-pushers who cannot explain the proof, the course is failing.

## 10. Let maintenance learn from users

User issues are evidence. They reveal:
- missing doc examples,
- missing aliases,
- hidden prerequisites,
- awkward notation,
- levels that are too broad,
- levels that are underexplained,
- or worlds whose dependencies are not actually clean.

A good author treats these reports as pedagogical diagnostics, not noise.
