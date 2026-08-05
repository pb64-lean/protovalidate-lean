#!/usr/bin/env bash
set -euo pipefail

harness=$1
executor=$2
expected_failures=$3

# The upstream harness exits 0 when the suite filter matches nothing (it
# early-returns on an empty case list and exits with the failure count), so
# its exit code alone cannot distinguish "all six bool cases passed" from "no
# cases ran".  Capture its report (printed to stderr) and additionally require
# the exact summary the six-case bool suite produces on a fully passing,
# non-verbose run.  A future corpus bump that renames or empties the suite
# fails here instead of going silently green.
status=0
output=$("$harness" \
  --suite '^standard_rules/bool$' \
  --strict_error \
  --strict_message \
  --expected_failures "$expected_failures" \
  "$executor" 2>&1) || status=$?

printf '%s\n' "$output"

if [[ "$status" -ne 0 ]]; then
  exit "$status"
fi

expected_summary='PASS (failed: 0, skipped: 0, passed: 6, total: 6)'
if [[ "$output" != *"$expected_summary"* ]]; then
  echo "supported_slice_test: harness exited 0 but did not report '$expected_summary';" \
    "the suite filter matched fewer cases than the supported slice requires" >&2
  exit 1
fi
