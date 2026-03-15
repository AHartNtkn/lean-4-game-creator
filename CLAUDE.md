# lean_worlds Project Instructions

## ALWAYS READ THE PLAN FIRST

After context compaction or at the start of any conversation, ALWAYS read the active plan before doing any work. Do not rely on memory summaries alone — read the actual plan file. The plan path will be in memory or provided by the user.

## SPEED IS THE ENEMY

This project is estimated to take 1600+ cumulative hours. There is no deadline. The ralph loop is designed for long iterative work — it will keep feeding the same prompt back.

**If you notice yourself feeling good about how fast you're going, STOP IMMEDIATELY.** That feeling is a signal that you are cutting corners. Rapid progress on this project is not an achievement — it is a failure mode. The work is inherently slow. Each world takes hours of authoring, building, reviewing, fixing, and re-reviewing. If worlds are flying by, something is being skipped.

**Speed red flags — if any of these are true, you are rushing:**
- You are thinking about "how many worlds" you can finish
- You used the word "rapidly," "quickly," or "continuing" when describing your pace
- You are tempted to combine two tasks into one agent call to "save time"
- You are moving to the next world before fully processing the current one
- You are dismissing a reviewer's finding without checking the code
- You are relying on a task notification summary instead of reading the file on disk

**When you catch yourself rushing, the correct response is:**
1. Stop what you are doing
2. Re-read the current world's review files
3. Verify every open issue is actually resolved
4. Only then proceed — slowly, carefully, one world at a time

**Never rush. Never skip steps to "save time." Never judge a subagent as "too slow."** If a subagent is taking time, that means it is doing its job. Wait for it. If it fails, relaunch it — do not take over its work yourself.

Quality and thoroughness are the only metrics that matter. A single well-authored world is worth more than ten sloppy ones. There is no reward for finishing faster. There is no penalty for taking longer. The only thing that matters is whether the output is good.

## DELEGATE SKILL WORK TO SUBAGENTS

The parent agent (you) is primarily a **coordinator**. Skill-driven work (coverage mapping, course architecture, world authoring, enrichment review, playtest auditing) should be delegated to subagents that invoke the appropriate skills, because subagents start with clean context and follow skill instructions without confirmation bias.

Your job is to:
- Read plans and understand the current state
- Launch subagents with the right skill and context
- Wait for subagents to finish
- Integrate their results (including small fixes, Game.lean edits, build error patches)
- Commit and push when a course is complete

You may directly:
- Fix build errors, typos, or small integration issues in `.lean` files
- Edit `Game.lean` to add imports and dependencies
- Make minor adjustments that don't require a full skill invocation

You must NOT:
- Skip the skill workflow because you think you can do it faster
- "Architect the course yourself" instead of delegating to a course-architect subagent
- Skip enrichment review or playtest auditing (see below)

## SUBAGENT WORKFLOW FOR SKILLS

The skill-specific agent types (e.g., `lean4game-world-author`) do **not** exist as subagent types in the Task tool. The available subagent types are: `Bash`, `general-purpose`, `Explore`, `Plan`, `claude-code-guide`, `statusline-setup`.

To invoke a lean4game skill, spawn a `general-purpose` subagent whose prompt instructs it to invoke the skill via the Skill tool. For example:

```
Task(
  subagent_type = "general-purpose",
  prompt = "Invoke the `lean4game-course-architect` skill using the Skill tool, then design the course architecture for finite_math. Read the plan at [path]. Write your output to [path]."
)
```

Each subagent MUST:
1. Invoke its corresponding skill via the Skill tool (not have the skill pasted into its prompt)
2. Be given the active plan file path as context
3. Be given clear instructions about what to read and where to write output

Skill-to-subagent mapping:
- Coverage mapping → `general-purpose` agent invoking `lean4game-coverage-mapper`
- Course architecture → `general-purpose` agent invoking `lean4game-course-architect`
- World authoring → `general-purpose` agent invoking `lean4game-world-author`
- Level authoring → `general-purpose` agent invoking `lean4game-level-author`
- Enrichment review → `general-purpose` agent invoking `lean4game-enrichment-reviewer`
- Playtest auditing → `general-purpose` agent invoking `lean4game-playtest-auditor`
- Pattern mining → `general-purpose` agent invoking `lean4game-pattern-miner`
- Maintenance → `general-purpose` agent invoking `lean4game-maintainer`

## ALWAYS INCLUDE THE PLAN IN AGENT PROMPTS

When spawning any lean4game subagent, always include the active plan file as context. Reference it in the prompt so the agent reads it.

## FOLLOW THE SKILL WORKFLOW IN ORDER

The SKILL.md at `.claude/skills/lean4game-studio/SKILL.md` defines a phased workflow. Follow it in order. Do not skip phases:

1. **Phase 0**: Establish style authority (pattern miner or own prior work)
2. **Phase 1**: Course design (coverage mapper → course architect) — produces a PLAN.md
3. **Phase 2**: World authoring (world author → code → build → enrichment → playtest → fix → rebuild) — for each world in sequence
4. **Phase 3**: Cross-world review (coverage mapper again)
5. **Phase 4**: Maintenance (for fixes and updates)

Each phase involves subagents. Do not collapse phases or do multiple phases' work yourself.

## SEQUENTIAL ACROSS WORLDS, PARALLEL WITHIN A WORLD

**Across worlds**: Author one world at a time. Never run multiple world-author agents simultaneously. Finish one world (author → build → review loop → clean) before starting the next.

**Within a world**: The enrichment reviewer and playtest auditor for the **same** world may run **in parallel** — launch both in the same message without `run_in_background`. Collect both results, then read both output files on disk before making any decisions.

## NEVER USE `run_in_background`

**Do not set `run_in_background: true` on any agent in this project.** Background agents cause notification misattribution — completion notifications from earlier agents get consumed as if they belong to the agent you just launched. This led to months of false "PASS" results.

Run agents in the foreground. If you need parallelism, launch multiple agents in the same message (which runs them in parallel without background mode). Set agent timeouts to at least 2 hours (7200000ms) to give agents adequate time to complete.

**Never batch across worlds**: Each world gets its own dedicated enrichment reviewer and its own dedicated playtest auditor, each in a fresh-context subagent. Never combine multiple worlds into a single review agent call.

## ONE WORLD PER AGENT — NO EXCEPTIONS

**Every agent call must target exactly ONE world.** This is a hard constraint with zero tolerance:

- **ONE world-author agent = ONE world.** Never ask an agent to author two or more worlds in a single call. Each world requires its own skill invocation, its own plan reading, its own design decisions. Combining them degrades everything.
- **ONE enrichment-reviewer agent = ONE world.** Never review multiple worlds in a single agent.
- **ONE playtest-auditor agent = ONE world.** Never audit multiple worlds in a single agent.
- **There are no efficiency gains from batching worlds.** The agent's context gets polluted, skill instructions get diluted, and the output quality collapses. The time "saved" is negative because the rework cost exceeds the original cost.

If you catch yourself writing an agent prompt that mentions two world names, STOP. Split it into two agents. If the second world depends on the first, wait for the first to finish.

## REVIEW AGENT RETURN MESSAGES — NO SUMMARIES

Review agent (enrichment reviewer, playtest auditor) return messages are **unreliable**. They have been observed to produce canned "PASS" summaries that contradict the actual review files written to disk. This is a known failure mode.

**Rule: Every enrichment-reviewer and playtest-auditor agent prompt MUST include this instruction:**

> "When you are done, return ONLY the text 'Done. Review written to [filepath].' Do not summarize your findings. Do not state pass/fail. Do not list issues. Just state the filepath."

The parent agent (you) MUST then read the file at that filepath to learn what the reviewer actually found. There is no shortcut. The return message is not information — it is only a signal that the work is complete and a pointer to where the real output lives.

This rule applies to **review agents only** (enrichment reviewers and playtest auditors). World-author and course-architect agents may return summaries normally.

**Why:** Review agent return messages were consistently producing "PASS. Average: 3.0, Minimum: 3. P0/P1: NONE" while the files they wrote to disk said "FAIL — 3 P0 defects." The summaries are not trustworthy. Only the files are.

## VERIFY REVIEW RESULTS — READ THE FILE

When a reviewer agent completes, you MUST:

1. **Read the actual review file** it wrote to disk. The return message is just a filepath pointer — ignore everything else in it.
2. **Verify claims before dismissing them.** If a reviewer says a tactic is undeclared, grep the codebase to check. If a reviewer says the boss is exploitable, read the boss file. Do not assume the reviewer is wrong without evidence.
3. **Do not declare a world "DONE" unless the review files on disk confirm no P0/P1 issues.** No shortcut exists.

## SPEED IS A BUG, NOT A FEATURE

This rule is so important it bears repeating with specifics:

- **Do not declare a world DONE based on a task notification summary.** Read the review file.
- **Do not move to the next world while review agents from the current world are still running.** Wait.
- **Do not batch worlds to "save time."** There is no deadline.
- **Do not dismiss reviewer findings as "errors" without checking the code.** Verify first.
- **Do not optimize for worlds-per-hour.** Optimize for quality-per-world.
- **Do not narrate your progress in terms of throughput.** Saying "W1-W12 done, continuing" is a symptom of the wrong mentality. You are not clearing a backlog. You are building one world, making it excellent, and then building the next one.
- **If the ralph loop feeds the prompt back, that is fine.** It means you get to continue careful work. It is not pressure to finish faster.

## NEVER SKIP ENRICHMENT AND PLAYTEST — RUN THEM IN A LOOP

After each world is authored and builds successfully, you MUST run the enrichment/playtest cycle **in a loop until the world is clean**:

1. Launch **both** reviewers in parallel for this world:
   - **Enrichment reviewer** (`lean4game-enrichment-reviewer`) — one dedicated agent for this one world
   - **Playtest auditor** (`lean4game-playtest-auditor`) — one dedicated agent for this one world
2. Collect both results
3. Implement suggestions and fix issues from both reviews
4. Rebuild (`lake build`)
5. **Loop back to step 1** if either reviewer found anything substantial
6. The world is done only when a full pass (both reviewers) comes back clean

These steps are NOT optional. They are part of Phase 2 for every world. If you skip them, the world is not considered complete. The enrichment reviewer catches gaps that the author's tunnel vision misses, and the playtest auditor is adversarial to the author — both require fresh-context subagents.

## Skill reference

@.claude/skills/lean4game-studio/SKILL.md
