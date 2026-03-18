#!/usr/bin/env bash
set -euo pipefail

HANK_DIR="$(cd "$(dirname "$0")" && pwd)"
DATA_DIR="$(cd "$(dirname "$0")/.." && pwd)"
EXEC_BASE="$HOME/.hankweave-executions/lean4game-studio"
MAX_PLAN_ROUNDS=5
MAX_REVIEW_ROUNDS=5

# Parse flags
NEW_EXEC=false
while [[ $# -gt 0 ]]; do
  case "$1" in
    --new) NEW_EXEC=true; shift ;;
    *) echo "Unknown flag: $1"; echo "Usage: run.sh [--new]"; exit 1 ;;
  esac
done

if [ "$NEW_EXEC" = true ]; then
  echo "Starting fresh execution directories..."
  rm -rf "$EXEC_BASE"
fi
mkdir -p "$EXEC_BASE"

# State directory — all progress lives here, survives across hank runs
STATE_DIR="$EXEC_BASE/state"
mkdir -p "$STATE_DIR"

# --- Helper functions ---

refresh_token() {
  echo "  Refreshing OAuth token..."
  echo "Hi" | claude --model haiku -p "Say ok" > /dev/null 2>&1 || true
  TOKEN=$(python3 -c "import json; print(json.load(open('$HOME/.claude/.credentials.json'))['claudeAiOauth']['accessToken'])" 2>/dev/null || true)
  if [ -z "$TOKEN" ]; then
    echo "ERROR: Could not extract OAuth token. Run 'claude auth login' and retry."
    exit 1
  fi
  export CLAUDE_CODE_OAUTH_TOKEN="$TOKEN"
}

run_hank() {
  local hank_file="$1"
  local exec_name="$2"
  local exec_dir="$EXEC_BASE/$exec_name"
  mkdir -p "$exec_dir"

  # Copy state files into the data dir so the hank can read them
  cp "$STATE_DIR"/*.json "$DATA_DIR/" 2>/dev/null || true
  cp "$STATE_DIR"/*.txt "$DATA_DIR/" 2>/dev/null || true

  refresh_token
  echo "  Running: $(basename "$hank_file") -> $exec_name"
  ~/.bun/bin/bunx hankweave "$hank_file" "$DATA_DIR" -e "$exec_dir" --force -n || {
    echo "  WARNING: Hank exited with error. Continuing..."
  }

  # Copy state files back from data dir (the hank may have updated them)
  for f in pipeline-state.json catalog-progress.json current-course.txt current-world.txt world-progress.json; do
    [ -f "$DATA_DIR/$f" ] && cp "$DATA_DIR/$f" "$STATE_DIR/"
  done
}

read_state() {
  local field="$1"
  python3 -c "import json; print(json.load(open('$STATE_DIR/pipeline-state.json')).get('$field', ''))" 2>/dev/null || echo ""
}

read_json_field() {
  local file="$1"
  local field="$2"
  python3 -c "import json; print(json.load(open('$file')).get('$field', ''))" 2>/dev/null || echo ""
}

update_state() {
  local key="$1"
  local value="$2"
  python3 -c "
import json
f = '$STATE_DIR/pipeline-state.json'
s = json.load(open(f))
s['$key'] = json.loads('$value')
json.dump(s, open(f, 'w'), indent=2)
"
}

archive_reviews() {
  local course="$1"
  local world="$2"
  local reviews_dir="$DATA_DIR/$course/reviews"
  for f in enrichment-current.md playtest-current.md gate-decision.json; do
    if [ -f "$reviews_dir/$f" ]; then
      local ext="${f##*.}"
      local base="${f%-current.*}"
      [ "$f" = "gate-decision.json" ] && base="gate"
      mv "$reviews_dir/$f" "$reviews_dir/${base}-${world}-final.${ext}" 2>/dev/null || true
    fi
  done
}

archive_plan_reviews() {
  local course="$1"
  local round="$2"
  local reviews_dir="$DATA_DIR/$course/reviews"
  for f in plan-review-current.md plan-gate-decision.json; do
    if [ -f "$reviews_dir/$f" ]; then
      local ext="${f##*.}"
      local base="${f%-current.*}"
      [ "$f" = "plan-gate-decision.json" ] && base="plan-gate"
      cp "$reviews_dir/$f" "$reviews_dir/${base}-round${round}-final.${ext}" 2>/dev/null || true
    fi
  done
}

# --- Initialize state files if missing ---

[ -f "$STATE_DIR/pipeline-state.json" ] || echo '{"currentCourse":null,"currentWorld":null,"reviewRound":0,"coursesCompleted":[],"worldsCompleted":[],"reviewCycleCount":0}' > "$STATE_DIR/pipeline-state.json"
[ -f "$STATE_DIR/catalog-progress.json" ] || echo '{"completed":[]}' > "$STATE_DIR/catalog-progress.json"

# --- Main loop ---

while true; do
  # Check if we have a course in progress
  COURSE=$(read_state "currentCourse")

  if [ -z "$COURSE" ] || [ "$COURSE" = "None" ]; then
    # No course in progress — select one
    echo ""
    echo "=========================================="
    echo "  Selecting next course...  $(date)"
    echo "=========================================="
    run_hank "$HANK_DIR/select-course.hank.json" "select-course"

    # Read what was selected
    if [ -f "$STATE_DIR/current-course.txt" ]; then
      COURSE=$(cat "$STATE_DIR/current-course.txt" | tr -d '[:space:]')
    else
      COURSE=$(read_state "currentCourse")
    fi

    if [ -z "$COURSE" ] || [ "$COURSE" = "None" ] || [ "$COURSE" = "ALL_COURSES_COMPLETE" ]; then
      echo ""
      echo "=========================================="
      echo "  ALL COURSES COMPLETE"
      echo "=========================================="
      break
    fi

    echo "  Selected: $COURSE"
  fi

  echo ""
  echo "=========================================="
  echo "  COURSE: $COURSE  $(date)"
  echo "=========================================="

  mkdir -p "$DATA_DIR/$COURSE/reviews"

  # --- Check what phase we're in ---
  # If PLAN.md doesn't exist, we need Phase 1
  # If world-list.txt doesn't exist, we need Phase 1
  # If world-progress.json has incomplete worlds, we're in Phase 2
  # Otherwise, Phase 3 + commit

  PLAN_FILE="$DATA_DIR/$COURSE/PLAN.md"
  WORLD_LIST="$DATA_DIR/$COURSE/world-list.txt"

  # --- Phase 1: Coverage map + Course architecture ---
  if [ ! -f "$PLAN_FILE" ] || [ ! -f "$WORLD_LIST" ]; then
    echo ""
    echo "--- Phase 1: Design ---"
    run_hank "$HANK_DIR/phase1.hank.json" "phase1"

    # --- Plan review loop ---
    echo ""
    echo "--- Plan Review ---"
    PLAN_PASSED=false
    for round in $(seq 1 $MAX_PLAN_ROUNDS); do
      echo "  Plan review round $round/$MAX_PLAN_ROUNDS"
      update_state "reviewCycleCount" "$((round - 1))"
      update_state "reviewRound" "$round"

      run_hank "$HANK_DIR/plan-review.hank.json" "plan-review"

      GATE_FILE="$DATA_DIR/$COURSE/reviews/plan-gate-decision.json"
      if [ ! -f "$GATE_FILE" ]; then
        echo "  WARNING: plan-gate-decision.json not found, retrying..."
        continue
      fi

      GATE_ACTION=$(read_json_field "$GATE_FILE" "action")
      echo "  Gate decision: $GATE_ACTION"
      archive_plan_reviews "$COURSE" "$round"

      if [ "$GATE_ACTION" = "done" ]; then
        PLAN_PASSED=true
        break
      elif [ "$GATE_ACTION" = "abort" ]; then
        echo "FATAL: Plan review aborted for $COURSE after $round rounds"
        exit 1
      fi
    done

    if [ "$PLAN_PASSED" = false ]; then
      echo "FATAL: Plan review did not pass after $MAX_PLAN_ROUNDS rounds for $COURSE"
      exit 1
    fi
  fi

  # --- Phase 2: World authoring ---
  if [ ! -f "$WORLD_LIST" ]; then
    echo "FATAL: $WORLD_LIST not found after Phase 1."
    exit 1
  fi

  # Initialize world progress if missing
  [ -f "$STATE_DIR/world-progress.json" ] || echo '{"completed":[],"current":null}' > "$STATE_DIR/world-progress.json"

  echo ""
  echo "--- Phase 2: World Authoring ---"
  while IFS= read -r WORLD || [ -n "$WORLD" ]; do
    WORLD=$(echo "$WORLD" | tr -d '[:space:]')
    [ -z "$WORLD" ] && continue

    # Skip already completed worlds
    ALREADY_DONE=$(python3 -c "import json; print('yes' if '$WORLD' in json.load(open('$STATE_DIR/world-progress.json')).get('completed',[]) else 'no')" 2>/dev/null || echo "no")
    if [ "$ALREADY_DONE" = "yes" ]; then
      echo "  === World: $WORLD (already complete, skipping) ==="
      continue
    fi

    echo ""
    echo "  === World: $WORLD ==="

    echo "$WORLD" > "$STATE_DIR/current-world.txt"
    update_state "currentWorld" "\"$WORLD\""
    update_state "reviewRound" "0"
    update_state "reviewCycleCount" "0"

    # Author + build
    echo "  Authoring..."
    run_hank "$HANK_DIR/author.hank.json" "author"

    # Review loop
    WORLD_PASSED=false
    for review_round in $(seq 1 $MAX_REVIEW_ROUNDS); do
      echo "  Review round $review_round/$MAX_REVIEW_ROUNDS"
      update_state "reviewRound" "$review_round"
      update_state "reviewCycleCount" "$review_round"

      run_hank "$HANK_DIR/review.hank.json" "review"

      GATE_FILE="$DATA_DIR/$COURSE/reviews/gate-decision.json"
      if [ ! -f "$GATE_FILE" ]; then
        echo "  WARNING: gate-decision.json not found, retrying..."
        continue
      fi

      GATE_ACTION=$(read_json_field "$GATE_FILE" "action")
      echo "  Gate decision: $GATE_ACTION"

      if [ "$GATE_ACTION" = "done" ]; then
        WORLD_PASSED=true
        break
      elif [ "$GATE_ACTION" = "abort" ]; then
        echo "FATAL: World $WORLD stuck after $review_round review rounds"
        exit 1
      fi
    done

    if [ "$WORLD_PASSED" = false ]; then
      echo "FATAL: World $WORLD did not pass after $MAX_REVIEW_ROUNDS rounds"
      exit 1
    fi

    # Mark world complete
    python3 -c "
import json
wp = json.load(open('$STATE_DIR/world-progress.json'))
wp['completed'].append('$WORLD')
wp['current'] = None
json.dump(wp, open('$STATE_DIR/world-progress.json', 'w'), indent=2)
"
    archive_reviews "$COURSE" "$WORLD"
    echo "  World $WORLD: PASSED"

  done < "$WORLD_LIST"

  # --- Phase 3: Cross-world review ---
  echo ""
  echo "--- Phase 3: Cross-World Review ---"
  run_hank "$HANK_DIR/phase3.hank.json" "phase3"

  # --- Commit + push ---
  echo ""
  echo "--- Committing $COURSE ---"
  cd "$DATA_DIR"
  git add -A
  git commit -m "Complete $COURSE course

Authored all worlds, passed plan review, enrichment review and playtest
audit for each world, passed cross-world coverage review.

Co-Authored-By: Claude <noreply@anthropic.com>" || echo "  Nothing to commit"
  git push || echo "  Push failed, continuing..."

  # Update catalog progress
  python3 -c "
import json
cp = json.load(open('$STATE_DIR/catalog-progress.json'))
cp['completed'].append('$COURSE')
json.dump(cp, open('$STATE_DIR/catalog-progress.json', 'w'), indent=2)
"

  # Clear current course so the next iteration selects a new one
  update_state "currentCourse" "null"
  update_state "currentWorld" "null"
  rm -f "$STATE_DIR/world-progress.json" "$STATE_DIR/current-world.txt"

  echo ""
  echo "=== $COURSE: COMPLETE ==="

done
