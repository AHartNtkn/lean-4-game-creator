# lean_worlds Project Instructions

## ALWAYS READ THE PLAN FIRST

After context compaction or at the start of any conversation, ALWAYS read the active plan before doing any work. Do not rely on memory summaries alone — read the actual plan file. The plan path will be in memory or provided by the user.

## NEVER USE GENERAL PURPOSE AGENTS! ALWAYS USE THE SKILL-SPECIFIC ONES!

When the lean4game studio skill pack is loaded, ALWAYS use the skill-specific agent types (e.g., `lean4game-world-author`, `lean4game-playtest-auditor`, `lean4game-enrichment-reviewer`) instead of `general-purpose` agents. The skill-specific agents have specialized prompts and knowledge that general-purpose agents lack. Using general-purpose agents as substitutes is forbidden.

## AGENTS MUST INVOKE THEIR ASSOCIATED SKILL

When spawning a subagent for a lean4game task, the agent prompt MUST instruct the agent to invoke its corresponding skill via the Skill tool. For example:

- World authoring agent → must invoke `lean4game-world-author` skill
- Playtest auditing agent → must invoke `lean4game-playtest-auditor` skill
- Enrichment review agent → must invoke `lean4game-enrichment-reviewer` skill
- Coverage mapping agent → must invoke `lean4game-coverage-mapper` skill

Do NOT paste skill instructions into the agent prompt manually. The agent loads the skill itself.

## ALWAYS INCLUDE THE PLAN IN AGENT PROMPTS

When spawning any lean4game subagent, always include the active plan file as context. Reference it in the prompt so the agent reads it.

## Skill reference

@.claude/skills/lean4game-studio/SKILL.md
