#!/usr/bin/env bash
set -euo pipefail

harness=$1
executor=$2
expected_failures=$3

"$harness" \
  --suite '^standard_rules/bool$' \
  --strict_error \
  --strict_message \
  --expected_failures "$expected_failures" \
  "$executor"
