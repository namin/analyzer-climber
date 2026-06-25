#!/usr/bin/env bash
# Build the artifact (runs every #guard / #guard_msgs check) and print the
# demo transcript.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== lake build =="
lake build

echo
echo "== AnalyzerClimber/Demo.lean =="
lake env lean AnalyzerClimber/Demo.lean
