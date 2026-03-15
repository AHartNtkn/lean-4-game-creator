# lean_worlds Project Instructions

## ALWAYS READ THE PLAN FIRST

After context compaction or at the start of any conversation, ALWAYS read the active plan before doing any work. Do not rely on memory summaries alone — read the actual plan file. The plan path will be in memory or provided by the user.

## THIS PROJECT IS NOT URGENT

This project is estimated to take 1600+ cumulative hours. There is no deadline. The ralph loop is designed for long iterative work — it will keep feeding the same prompt back.

**Never rush. Never skip steps to "save time." Never judge a subagent as "too slow."** If a subagent is taking time, that means it is doing its job. Wait for it. If it fails, relaunch it — do not take over its work yourself.

Quality and thoroughness are the only metrics that matter. A single well-authored world is worth more than ten sloppy ones.

## NEVER WRITE COURSE CODE DIRECTLY

The parent agent (you) is a **coordinator**. You do not write level files, world files, or Game.lean edits yourself. All course content authoring is done by subagents invoking the appropriate skills.

Your job is to:
- Read plans and understand the current state
- Launch subagents with the right skill and context
- Wait for subagents to finish
- Integrate their results
- Commit and push when a course is complete

You must NEVER:
- Edit level `.lean` files directly
- Skip the skill workflow because you think you can do it faster
- Modify stub/placeholder files (like Welcome levels) outside the skill workflow
- "Architect the course yourself" instead of delegating to a course-architect subagent

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

## Skill reference

@.claude/skills/lean4game-studio/SKILL.md
