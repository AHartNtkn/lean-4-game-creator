#!/usr/bin/env bash
set -euo pipefail

# lean4game local development server
# Ensures all prerequisites (mathlib, gamedata) are met, generates the catalog
# config, and starts the server.
#
# Usage:
#   ./serve.sh   # build all courses, then start server
#
# Restart: just run ./serve.sh again — it kills any previous instance automatically.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN4GAME_DIR="$SCRIPT_DIR/lean4game"
MATHLIB_DIR="$SCRIPT_DIR/mathlib4"
CONFIG_JSON="$LEAN4GAME_DIR/client/src/config.json"
MATHLIB_REPO="https://github.com/leanprover-community/mathlib4.git"
PIDFILE="$SCRIPT_DIR/.serve.pid"

# Ports — chosen to avoid common dev server conflicts (3000, 5173, 8080)
RELAY_PORT="${LEAN4GAME_RELAY_PORT:-9080}"
CLIENT_PORT="${LEAN4GAME_CLIENT_PORT:-9000}"

# --- Helpers ---

die() { echo "❌ $*" >&2; exit 1; }

# Kill any previous instance: PID file first, then anything on our ports.
kill_previous() {
  # Try PID file
  if [[ -f "$PIDFILE" ]]; then
    local old_pid
    old_pid=$(cat "$PIDFILE")
    if kill -0 "$old_pid" 2>/dev/null; then
      echo "Stopping previous server (pid $old_pid)..."
      kill -- -"$old_pid" 2>/dev/null || kill "$old_pid" 2>/dev/null || true
    fi
    rm -f "$PIDFILE"
  fi

  # Kill anything still on our ports
  local port pid
  for port in "$RELAY_PORT" "$CLIENT_PORT"; do
    pid=$(ss -tlnp "sport = :$port" 2>/dev/null | grep -oP 'pid=\K\d+' | head -1 || true)
    if [[ -n "$pid" ]]; then
      echo "Killing process on port $port (pid $pid)..."
      kill "$pid" 2>/dev/null || true
    fi
  done

  # Wait for ports to clear
  local attempts=0
  while (( attempts < 10 )); do
    local busy=false
    for port in "$RELAY_PORT" "$CLIENT_PORT"; do
      if ss -tlnp "sport = :$port" 2>/dev/null | grep -q 'pid='; then
        busy=true
        break
      fi
    done
    [[ "$busy" = false ]] && break
    sleep 1
    attempts=$((attempts + 1))
  done
}

# Clean up PID file on exit.
cleanup() { rm -f "$PIDFILE"; }
trap cleanup EXIT


# Discover all course directories (those containing Game.lean).
discover_courses() {
  for game_lean in "$SCRIPT_DIR"/*/Game.lean; do
    basename "$(dirname "$game_lean")"
  done | sort
}

# Generate config.json with all local courses in the catalog.
generate_config() {
  local courses=("$@")
  local entries=""
  for course in "${courses[@]}"; do
    [[ -n "$entries" ]] && entries="$entries,"$'\n'
    entries="$entries    \"local/$course\""
  done

  cat > "$CONFIG_JSON" <<EOF
{
  "allGames": [
$entries
  ],
  "languages": [
    {"iso": "en", "flag": "GB", "name": "English"}
  ],
  "useFlags": false
}
EOF
}

# Determine which mathlib4 branch matches the courses' lean-toolchain.
mathlib_branch() {
  # Read the lean version from any course (all share the same toolchain)
  local toolchain
  toolchain=$(head -1 "$SCRIPT_DIR"/*/lean-toolchain 2>/dev/null | head -1)

  # Check if mathlib4 master matches
  local master_toolchain
  master_toolchain=$(gh api repos/leanprover-community/mathlib4/contents/lean-toolchain \
    -q '.content' 2>/dev/null | base64 -d | tr -d '[:space:]') || true

  if [[ "$master_toolchain" == "$toolchain" ]]; then
    echo "master"
    return
  fi

  # Otherwise fall back to master and let the build fail with a clear error
  echo "master"
}

# --- Kill previous instance ---

kill_previous

# --- Ensure mathlib4 exists with build cache ---

mathlib_needs_setup() {
  # Not cloned at all
  [[ -d "$MATHLIB_DIR" ]] || return 0
  # Cloned but cache not fetched: fewer oleans than source files means incomplete
  local olean_count src_count
  olean_count=$(find "$MATHLIB_DIR/.lake/build" -name '*.olean' 2>/dev/null | wc -l)
  src_count=$(find "$MATHLIB_DIR/Mathlib" -name '*.lean' 2>/dev/null | wc -l)
  # Cache should have at least 90% of source files as oleans
  if [[ "$src_count" -gt 0 ]] && (( olean_count * 100 / src_count < 90 )); then
    return 0
  fi
  return 1
}

if mathlib_needs_setup; then
  if [[ ! -d "$MATHLIB_DIR" ]]; then
    branch=$(mathlib_branch)
    echo "Fetching mathlib4 (branch: $branch)..."
    git clone --branch "$branch" --depth 1 "$MATHLIB_REPO" "$MATHLIB_DIR"
  fi

  echo "Fetching mathlib4 build cache..."
  (cd "$MATHLIB_DIR" && lake -R exe cache get) || die "lake exe cache get failed"
  echo "✅ mathlib4 ready"
  echo ""
fi

# --- Discover courses ---

mapfile -t ALL_COURSES < <(discover_courses)
echo "Found ${#ALL_COURSES[@]} courses"

# --- Build all courses ---

failed=()
for course in "${ALL_COURSES[@]}"; do
  echo "Building $course..."
  (cd "$SCRIPT_DIR/$course" && lake build) || {
    echo "  ❌ lake build failed for $course — skipping"
    failed+=("$course")
    continue
  }
done

if [[ ${#failed[@]} -gt 0 ]]; then
  echo ""
  echo "${#failed[@]} course(s) failed to build:"
  printf "  %s\n" "${failed[@]}"
  echo ""
fi

# --- Generate catalog config ---

generate_config "${ALL_COURSES[@]}"
echo "Generated catalog with ${#ALL_COURSES[@]} courses"

# --- Preflight checks ---

[[ -d "$LEAN4GAME_DIR" ]] || die "lean4game/ directory not found"
[[ -f "$LEAN4GAME_DIR/package.json" ]] || die "lean4game/package.json not found — is the submodule initialized?"


if [[ ! -f "$LEAN4GAME_DIR/relay/dist/src/index.js" ]]; then
  echo "Compiling relay..."
  (cd "$LEAN4GAME_DIR" && npx tsc -b ./relay)
fi

# --- Start ---

echo ""
echo "Starting lean4game server"
echo "  Client: http://localhost:$CLIENT_PORT"
echo "  Relay:  http://localhost:$RELAY_PORT"
echo ""

export PORT="$RELAY_PORT"
export CLIENT_PORT="$CLIENT_PORT"

# Record our PID so the next ./serve.sh can kill us.
echo $$ > "$PIDFILE"

cd "$LEAN4GAME_DIR"
exec npm start
