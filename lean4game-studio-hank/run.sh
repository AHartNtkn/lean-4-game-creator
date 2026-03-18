#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
PROMPTS="$SCRIPT_DIR/prompts"
STATE_DIR="$PROJECT_DIR/.studio-state"
MAX_PLAN_ROUNDS=5
MAX_REVIEW_ROUNDS=5
ALLOWED_TOOLS="Read,Edit,Write,Bash,Glob,Grep,WebSearch,WebFetch"

# Parse flags
NEW_RUN=false
while [[ $# -gt 0 ]]; do
  case "$1" in
    --new) NEW_RUN=true; shift ;;
    *) echo "Unknown flag: $1"; echo "Usage: run.sh [--new]"; exit 1 ;;
  esac
done

if [ "$NEW_RUN" = true ]; then
  echo "Starting fresh..."
  rm -rf "$STATE_DIR"
fi
mkdir -p "$STATE_DIR"

# --- Helper functions ---

step() {
  local prompt_file="$1"
  local description="$2"
  shift 2
  echo "  [$description]"
  cd "$PROJECT_DIR"
  claude -p "$(cat "$prompt_file")" \
    --allowedTools "$ALLOWED_TOOLS" \
    --model opus \
    "$@" \
    || {
      echo "  WARNING: claude exited with error during: $description"
      return 1
    }
}

read_json_field() {
  python3 -c "import json; print(json.load(open('$1')).get('$2', ''))" 2>/dev/null || echo ""
}

update_state() {
  python3 -c "
import json, os
f = '$STATE_DIR/state.json'
s = json.load(open(f)) if os.path.exists(f) else {}
s['$1'] = json.loads('$2')
json.dump(s, open(f, 'w'), indent=2)
"
}

read_state() {
  python3 -c "
import json, os
f = '$STATE_DIR/state.json'
s = json.load(open(f)) if os.path.exists(f) else {}
v = s.get('$1')
print('' if v is None else v)
" 2>/dev/null || echo ""
}

archive_reviews() {
  local course="$1" world="$2"
  local d="$PROJECT_DIR/$course/reviews"
  [ -f "$d/enrichment-current.md" ] && mv "$d/enrichment-current.md" "$d/enrichment-${world}-final.md" 2>/dev/null || true
  [ -f "$d/playtest-current.md" ] && mv "$d/playtest-current.md" "$d/playtest-${world}-final.md" 2>/dev/null || true
  [ -f "$d/gate-decision.json" ] && cp "$d/gate-decision.json" "$d/gate-${world}-final.json" 2>/dev/null || true
}

archive_plan_reviews() {
  local course="$1" round="$2"
  local d="$PROJECT_DIR/$course/reviews"
  [ -f "$d/plan-review-current.md" ] && cp "$d/plan-review-current.md" "$d/plan-review-round${round}.md" 2>/dev/null || true
  [ -f "$d/plan-gate-decision.json" ] && cp "$d/plan-gate-decision.json" "$d/plan-gate-round${round}.json" 2>/dev/null || true
}

# --- Initialize state ---

[ -f "$STATE_DIR/state.json" ] || echo '{}' > "$STATE_DIR/state.json"
[ -f "$STATE_DIR/catalog-progress.json" ] || echo '{"completed":[]}' > "$STATE_DIR/catalog-progress.json"

# --- Main loop ---

while true; do
  COURSE=$(read_state "currentCourse")

  if [ -z "$COURSE" ]; then
    echo ""
    echo "=========================================="
    echo "  Selecting next course...  $(date)"
    echo "=========================================="

    # Write state files the select-course prompt needs
    cp "$STATE_DIR/catalog-progress.json" "$PROJECT_DIR/catalog-progress.json"

    step "$PROMPTS/select-course.md" "select-course" --model haiku

    # Read result
    if [ -f "$PROJECT_DIR/current-course.txt" ]; then
      COURSE=$(cat "$PROJECT_DIR/current-course.txt" | tr -d '[:space:]')
    fi

    if [ -z "$COURSE" ] || [ "$COURSE" = "ALL_COURSES_COMPLETE" ]; then
      echo ""
      echo "  ALL COURSES COMPLETE"
      break
    fi

    # Validate: the course must be an existing directory with Game.lean
    if [ ! -f "$PROJECT_DIR/$COURSE/Game.lean" ]; then
      echo "  ERROR: select-course wrote '$COURSE' but $PROJECT_DIR/$COURSE/Game.lean does not exist."
      echo "  Available courses:"
      ls -d "$PROJECT_DIR"/*/Game.lean 2>/dev/null | sed "s|$PROJECT_DIR/||;s|/Game.lean||" | sed 's/^/    /'
      exit 1
    fi

    update_state "currentCourse" "\"$COURSE\""
    echo "  Selected: $COURSE"
  fi

  echo ""
  echo "=========================================="
  echo "  COURSE: $COURSE  $(date)"
  echo "=========================================="

  # Write context files that prompts read
  echo "$COURSE" > "$PROJECT_DIR/current-course.txt"
  mkdir -p "$PROJECT_DIR/$COURSE/reviews"

  PLAN_FILE="$PROJECT_DIR/$COURSE/PLAN.md"
  WORLD_LIST="$PROJECT_DIR/$COURSE/world-list.txt"

  # --- Phase 1: Design ---
  if [ ! -f "$PLAN_FILE" ] || [ ! -f "$WORLD_LIST" ]; then
    echo ""
    echo "--- Phase 1: Design ---"
    step "$PROMPTS/phase1-coverage-mapper.md" "coverage-map"
    step "$PROMPTS/phase1-course-architect.md" "course-architect"

    # --- Plan review loop ---
    echo ""
    echo "--- Plan Review ---"
    PLAN_PASSED=false
    for round in $(seq 1 $MAX_PLAN_ROUNDS); do
      echo "  Round $round/$MAX_PLAN_ROUNDS"

      step "$PROMPTS/phase1-plan-review.md" "plan-review"
      step "$PROMPTS/phase1-plan-gate.md" "plan-gate"

      GATE_FILE="$PROJECT_DIR/$COURSE/reviews/plan-gate-decision.json"
      if [ ! -f "$GATE_FILE" ]; then
        echo "  WARNING: plan-gate-decision.json not found"
        continue
      fi

      GATE_ACTION=$(read_json_field "$GATE_FILE" "action")
      echo "  Gate: $GATE_ACTION"
      archive_plan_reviews "$COURSE" "$round"

      if [ "$GATE_ACTION" = "done" ]; then
        PLAN_PASSED=true
        break
      elif [ "$GATE_ACTION" = "abort" ]; then
        echo "FATAL: Plan aborted after $round rounds"
        exit 1
      fi

      # Fix and loop
      step "$PROMPTS/phase1-plan-fix.md" "plan-fix"
    done

    if [ "$PLAN_PASSED" = false ]; then
      echo "FATAL: Plan did not pass after $MAX_PLAN_ROUNDS rounds"
      exit 1
    fi
  fi

  # --- Phase 2: World authoring ---
  if [ ! -f "$WORLD_LIST" ]; then
    echo "FATAL: $WORLD_LIST not found after Phase 1"
    exit 1
  fi

  [ -f "$STATE_DIR/world-progress.json" ] || echo '{"completed":[]}' > "$STATE_DIR/world-progress.json"

  echo ""
  echo "--- Phase 2: World Authoring ---"
  while IFS= read -r WORLD || [ -n "$WORLD" ]; do
    WORLD=$(echo "$WORLD" | tr -d '[:space:]')
    [ -z "$WORLD" ] && continue

    # Skip completed worlds
    DONE=$(python3 -c "import json; print('yes' if '$WORLD' in json.load(open('$STATE_DIR/world-progress.json')).get('completed',[]) else 'no')" 2>/dev/null || echo "no")
    if [ "$DONE" = "yes" ]; then
      echo "  $WORLD: already complete"
      continue
    fi

    echo ""
    echo "  === World: $WORLD ==="
    echo "$WORLD" > "$PROJECT_DIR/current-world.txt"
    update_state "currentWorld" "\"$WORLD\""

    # Author + build
    step "$PROMPTS/phase2-world-author.md" "author $WORLD"

    # Build
    cd "$PROJECT_DIR/$COURSE"
    lake build 2>&1 | tee "$PROJECT_DIR/build-log.txt"
    echo $? > "$PROJECT_DIR/build-exit-code.txt"
    cd "$PROJECT_DIR"

    BUILD_EXIT=$(cat "$PROJECT_DIR/build-exit-code.txt")
    if [ "$BUILD_EXIT" != "0" ]; then
      step "$PROMPTS/phase2-build.md" "build-fix $WORLD"
    fi

    # Review loop
    WORLD_PASSED=false
    for review_round in $(seq 1 $MAX_REVIEW_ROUNDS); do
      echo "  Review $review_round/$MAX_REVIEW_ROUNDS"

      step "$PROMPTS/phase2-enrichment-reviewer.md" "enrichment $WORLD r$review_round"
      step "$PROMPTS/phase2-playtest-auditor.md" "playtest $WORLD r$review_round"
      step "$PROMPTS/phase2-review-gate.md" "gate $WORLD r$review_round"

      GATE_FILE="$PROJECT_DIR/$COURSE/reviews/gate-decision.json"
      if [ ! -f "$GATE_FILE" ]; then
        echo "  WARNING: gate-decision.json not found"
        continue
      fi

      GATE_ACTION=$(read_json_field "$GATE_FILE" "action")
      echo "  Gate: $GATE_ACTION"

      if [ "$GATE_ACTION" = "done" ]; then
        WORLD_PASSED=true
        break
      elif [ "$GATE_ACTION" = "abort" ]; then
        echo "FATAL: $WORLD stuck after $review_round rounds"
        exit 1
      fi

      # Fix and loop
      step "$PROMPTS/phase2-fix-issues.md" "fix $WORLD r$review_round"
    done

    if [ "$WORLD_PASSED" = false ]; then
      echo "FATAL: $WORLD did not pass after $MAX_REVIEW_ROUNDS rounds"
      exit 1
    fi

    # Mark complete
    python3 -c "
import json
f = '$STATE_DIR/world-progress.json'
wp = json.load(open(f))
wp['completed'].append('$WORLD')
json.dump(wp, open(f, 'w'), indent=2)
"
    archive_reviews "$COURSE" "$WORLD"
    echo "  $WORLD: PASSED"

  done < "$WORLD_LIST"

  # --- Phase 3: Cross-world review ---
  echo ""
  echo "--- Phase 3: Cross-World Review ---"
  step "$PROMPTS/phase3-coverage-remap.md" "cross-world-coverage"
  step "$PROMPTS/phase3-cross-world-fix.md" "cross-world-fix"

  # --- Commit + push ---
  echo ""
  echo "--- Committing $COURSE ---"
  cd "$PROJECT_DIR"
  git add -A
  git commit -m "Complete $COURSE course

Co-Authored-By: Claude <noreply@anthropic.com>" || echo "  Nothing to commit"
  git push || echo "  Push failed"

  # Update progress
  python3 -c "
import json
f = '$STATE_DIR/catalog-progress.json'
cp = json.load(open(f))
cp['completed'].append('$COURSE')
json.dump(cp, open(f, 'w'), indent=2)
"

  # Clear for next course
  update_state "currentCourse" "null"
  update_state "currentWorld" "null"
  rm -f "$STATE_DIR/world-progress.json"

  echo ""
  echo "=== $COURSE: COMPLETE ==="

done
