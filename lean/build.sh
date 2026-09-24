#!/usr/bin/env bash
# One-command verification. No compiled project proofs are distributed.
set -euo pipefail
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$project_dir"
mkdir -p build-logs
rm -f build-logs/SUCCESS.txt
fail() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
run_logged() {
  local name=$1; shift
  if "$@" > "build-logs/$name.log" 2>&1; then return 0; else
    local status=$?
    printf '\nFAILED: %s (exit %s). See build-logs/%s.log\n' "$name" "$status" "$name" >&2
    tail -n 70 "build-logs/$name.log" >&2
    exit "$status"
  fi
}
for command_name in git curl tar; do
  command -v "$command_name" >/dev/null 2>&1 || fail "Install $command_name, then run ./build.sh again."
done
git --version >/dev/null 2>&1 || fail 'Git is not functional. Install Git / Xcode Command Line Tools, then rerun.'
if command -v sha256sum >/dev/null 2>&1; then
  checksum() { sha256sum "$@"; }
elif command -v shasum >/dev/null 2>&1; then
  checksum() { shasum -a 256 "$@"; }
else
  fail 'A SHA-256 utility is required (sha256sum or shasum).'
fi
run_logged source-integrity checksum -c SOURCES.sha256

# Use an installed elan, or install the pinned manager inside this project.
# No shell profile or global default toolchain is changed.
if [ -x "$project_dir/.tooling/elan/bin/elan" ]; then
  export ELAN_HOME="$project_dir/.tooling/elan"
  elan_command="$ELAN_HOME/bin/elan"
elif command -v elan >/dev/null 2>&1; then
  elan_command=$(command -v elan)
elif [ -x "${HOME:-}/.elan/bin/elan" ]; then
  elan_command="$HOME/.elan/bin/elan"
else
  case "$(uname -s):$(uname -m)" in
    Darwin:arm64|Darwin:aarch64)
      elan_target=aarch64-apple-darwin
      elan_digest=3b3170eb6af7d89e28c7a98d25066a07efb41246e43d6333505dfa54069100c8 ;;
    Darwin:x86_64)
      elan_target=x86_64-apple-darwin
      elan_digest=3bd377a1d767fabaad3b40d32bfa3d51b099ed40dbcd3c08ca66af2761ec1a70 ;;
    Linux:aarch64|Linux:arm64)
      elan_target=aarch64-unknown-linux-gnu
      elan_digest=bb78726ace6a912c7122a389018bcd69d9122ce04659800101392f7db380d3b3 ;;
    Linux:x86_64)
      elan_target=x86_64-unknown-linux-gnu
      elan_digest=4e717523217af592fa2d7b9c479410a31816c065d66ccbf0c2149337cfec0f5c ;;
    *) fail 'Automatic setup supports macOS and GNU/Linux (including WSL). Install elan on other systems.' ;;
  esac
  printf 'Installing elan 4.2.1 inside .tooling/ (no global settings changed)...\n'
  mkdir -p .tooling/installer
  curl --fail --location --retry 3 --output .tooling/installer/elan.tar.gz \
    "https://github.com/leanprover/elan/releases/download/v4.2.1/elan-$elan_target.tar.gz"
  printf '%s  %s\n' "$elan_digest" '.tooling/installer/elan.tar.gz' > .tooling/installer/SHA256SUMS
  run_logged elan-download-integrity checksum -c .tooling/installer/SHA256SUMS
  tar -xzf .tooling/installer/elan.tar.gz -C .tooling/installer
  export ELAN_HOME="$project_dir/.tooling/elan"
  run_logged elan-install .tooling/installer/elan-init -y --no-modify-path --default-toolchain none
  elan_command="$ELAN_HOME/bin/elan"
fi
pinned_toolchain=$(tr -d '\r\n' < lean-toolchain)
export ELAN_TOOLCHAIN="$pinned_toolchain"
export LEAN_NUM_THREADS=1
# Never inherit user search paths that could substitute external proof modules.
unset LEAN_PATH LEAN_SRC_PATH LAKE_OVERRIDE_LEAN LEAN_SYSROOT LEAN LAKE_HOME
unset LEAN_GITHASH LEAN_AR LEAN_CC
lake_cmd() { "$elan_command" run --install "$pinned_toolchain" lake "$@"; }
printf 'Preparing %s and the pinned Mathlib dependencies...\n' "$pinned_toolchain"
run_logged lean-version "$elan_command" run --install "$pinned_toolchain" lean --version
run_logged dependency-cache lake_cmd exe cache get
while read -r package_name expected_revision; do
  actual_revision=$(git -C ".lake/packages/$package_name" rev-parse HEAD)
  [ "$actual_revision" = "$expected_revision" ] || fail "Dependency revision mismatch: $package_name"
done < dependency-pins.txt
run_logged pinned-input-integrity checksum -c SOURCES.sha256

module_total=$(wc -l < build-order.txt | tr -d ' ')
module_index=0
while IFS= read -r module_name; do
  [ -n "$module_name" ] || continue
  case "$module_name" in *[!A-Za-z0-9_.]*) fail 'Invalid module in build-order.txt.' ;; esac
  module_index=$((module_index + 1))
  printf '[%s/%s] Checking %s\n' "$module_index" "$module_total" "$module_name"
  run_logged "$module_name" lake_cmd build "+$module_name"
done < build-order.txt
# Also exercise the normal public default target, which includes Verification.
run_logged default-build lake_cmd build
# Fresh elaboration displays the final statements and executes the axiom guards.
run_logged final-verification lake_cmd env lean Verification.lean
run_logged final-source-integrity checksum -c SOURCES.sha256
{
  printf 'SUCCESS: all project proof modules compiled and the final axiom guards passed.\n'
  printf 'Toolchain: %s\n' "$pinned_toolchain"
  printf 'Verified declarations:\n'
  cat THEOREMS.txt
  printf 'Standard axioms only: propext, Classical.choice, Quot.sound.\n'
  if [ -f AMBIENT_SCOPE.txt ]; then cat AMBIENT_SCOPE.txt; fi
} > build-logs/SUCCESS.txt
cat build-logs/SUCCESS.txt
printf '\nStatements and axiom output: build-logs/final-verification.log\n'
