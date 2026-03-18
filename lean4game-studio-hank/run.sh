#!/usr/bin/env bash
set -euo pipefail

HANK_DIR="$(cd "$(dirname "$0")" && pwd)"
DATA_DIR="$(cd "$(dirname "$0")/.." && pwd)"
EXEC_BASE="$HOME/.hankweave-executions/lean4game-studio"
MAX_PLAN_ROUNDS=5
MAX_REVIEW_ROUNDS=5
NEW_EXEC=false

# Parse flags
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

# Course priority order (prerequisites first, well-covered first, basic first)
COURSE_ORDER=(
  finite_math functions_relations orders_lattices algebraic_structures
  group_theory_1 ring_theory linear_algebra_1 field_galois
  category_theory_1 general_topology elementary_nt combinatorics
  computability model_theory_1 set_theory_1
  group_theory_2 linear_algebra_2 commutative_algebra_1 representation_theory
  lie_algebras metric_spaces real_analysis measure_theory
  category_theory_2 model_theory_2 set_theory_2
  complex_analysis functional_analysis probability
  commutative_algebra_2 homological_algebra algebra_seminar
  topological_algebra manifolds convex_geometry
  analytic_nt algebraic_nt advanced_combinatorics
  fourier_odes dynamics sheaves_topoi
  algebraic_topology algebraic_geometry_1
  descriptive_set metamathematics
  algebraic_geometry_2 condensed information_theory
  functors_monads
)

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
  refresh_token
  echo "  Running: $(basename "$hank_file") -> $exec_name"
  ~/.bun/bin/bunx hankweave "$hank_file" "$DATA_DIR" -e "$exec_dir" --force -n || {
    echo "  WARNING: Hank exited with error. Continuing..."
    return 0
  }
}

update_state() {
  local key="$1"
  local value="$2"
  python3 -c "
import json
f = '$DATA_DIR/pipeline-state.json'
s = json.load(open(f))
s['$key'] = json.loads('$value')
json.dump(s, open(f, 'w'), indent=2)
"
}

read_json_field() {
  local file="$1"
  local field="$2"
  python3 -c "import json; print(json.load(open('$file')).get('$field', ''))" 2>/dev/null || echo ""
}

is_course_complete() {
  local course="$1"
  python3 -c "
import json
cp = json.load(open('$DATA_DIR/catalog-progress.json'))
print('yes' if '$course' in cp.get('completed', []) else 'no')
" 2>/dev/null
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

# --- Initialize state files ---

[ -f "$DATA_DIR/pipeline-state.json" ] || echo '{"currentCourse":null,"currentWorld":null,"reviewRound":0,"coursesCompleted":[],"worldsCompleted":[],"reviewCycleCount":0}' > "$DATA_DIR/pipeline-state.json"
[ -f "$DATA_DIR/catalog-progress.json" ] || echo '{"completed":[]}' > "$DATA_DIR/catalog-progress.json"

# --- Main course loop ---

for COURSE in "${COURSE_ORDER[@]}"; do
  # Skip completed courses
  if [ "$(is_course_complete "$COURSE")" = "yes" ]; then
    echo "=== $COURSE: already complete, skipping ==="
    continue
  fi

  # Skip courses whose directory doesn't exist
  if [ ! -d "$DATA_DIR/$COURSE" ]; then
    echo "=== $COURSE: directory not found, skipping ==="
    continue
  fi

  echo ""
  echo "=========================================="
  echo "  COURSE: $COURSE  $(date)"
  echo "=========================================="

  # Update state
  update_state "currentCourse" "\"$COURSE\""
  update_state "currentWorld" "null"
  update_state "reviewRound" "0"
  update_state "reviewCycleCount" "0"
  update_state "worldsCompleted" "[]"
  echo "$COURSE" > "$DATA_DIR/current-course.txt"
  mkdir -p "$DATA_DIR/$COURSE/reviews"

  # --- Phase 1: Coverage map + Course architecture ---
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

    # Check gate decision
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
    # "continue" → loop
  done

  if [ "$PLAN_PASSED" = false ]; then
    echo "FATAL: Plan review did not pass after $MAX_PLAN_ROUNDS rounds for $COURSE"
    exit 1
  fi

  # --- Read world list ---
  WORLD_LIST="$DATA_DIR/$COURSE/world-list.txt"
  if [ ! -f "$WORLD_LIST" ]; then
    echo "FATAL: $WORLD_LIST not found. The course-architect prompt must produce this file."
    exit 1
  fi

  echo '{"completed":[],"current":null}' > "$DATA_DIR/world-progress.json"

  # --- World loop ---
  echo ""
  echo "--- Phase 2: World Authoring ---"
  while IFS= read -r WORLD || [ -n "$WORLD" ]; do
    WORLD=$(echo "$WORLD" | tr -d '[:space:]')
    [ -z "$WORLD" ] && continue

    echo ""
    echo "  === World: $WORLD ==="

    echo "$WORLD" > "$DATA_DIR/current-world.txt"
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

      # Check gate decision
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
      # "continue" → loop
    done

    if [ "$WORLD_PASSED" = false ]; then
      echo "FATAL: World $WORLD did not pass after $MAX_REVIEW_ROUNDS rounds"
      exit 1
    fi

    # Mark world complete
    python3 -c "
import json
wp = json.load(open('$DATA_DIR/world-progress.json'))
wp['completed'].append('$WORLD')
wp['current'] = None
json.dump(wp, open('$DATA_DIR/world-progress.json', 'w'), indent=2)
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
cp = json.load(open('$DATA_DIR/catalog-progress.json'))
cp['completed'].append('$COURSE')
json.dump(cp, open('$DATA_DIR/catalog-progress.json', 'w'), indent=2)
"
  echo ""
  echo "=== $COURSE: COMPLETE ==="

done

echo ""
echo "=========================================="
echo "  ALL COURSES COMPLETE"
echo "=========================================="
