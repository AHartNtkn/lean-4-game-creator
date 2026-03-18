#!/usr/bin/env bash
set -euo pipefail

HANK_JSON="$(cd "$(dirname "$0")" && pwd)/hank.json"
DATA_DIR="$(cd "$(dirname "$0")/.." && pwd)"
MAX_RUNS="${1:-50}"

# Find the most recent execution directory, or let hankweave create one
EXEC_DIR=$(ls -td ~/.hankweave-executions/*/ 2>/dev/null | head -1 || true)

for i in $(seq 1 "$MAX_RUNS"); do
  echo ""
  echo "=========================================="
  echo "  Run $i / $MAX_RUNS  $(date)"
  echo "=========================================="

  # Refresh OAuth token from Claude Code credentials
  TOKEN=$(python3 -c "import json; print(json.load(open('$HOME/.claude/.credentials.json'))['claudeAiOauth']['accessToken'])" 2>/dev/null || true)

  if [ -z "$TOKEN" ]; then
    echo "ERROR: Could not extract OAuth token. Run 'claude auth login' and retry."
    exit 1
  fi

  export CLAUDE_CODE_OAUTH_TOKEN="$TOKEN"

  # Build the command
  CMD=(~/.bun/bin/bunx hankweave "$HANK_JSON" "$DATA_DIR")
  if [ -n "$EXEC_DIR" ]; then
    CMD+=(-e "$EXEC_DIR" --force)
  fi

  # Run hankweave — it will exit when the token expires or it finishes
  "${CMD[@]}" || true

  # Capture the execution directory for subsequent runs
  EXEC_DIR=$(ls -td ~/.hankweave-executions/*/ 2>/dev/null | head -1 || true)

  echo ""
  echo "Hankweave exited. Refreshing OAuth token via Claude Code..."

  # Force a Claude Code call to refresh the OAuth token in ~/.claude/.credentials.json
  echo "Hi" | claude --model haiku -p "Say ok" > /dev/null 2>&1 || true

  sleep 5
done

echo ""
echo "Completed $MAX_RUNS runs."
