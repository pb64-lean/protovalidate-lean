#!/usr/bin/env bash
set -euo pipefail

module_file=$1
patch_file=$2
registry_file=$3
shift 3

if ! grep -Fq 'bazel_dep(name = "protovalidate", version = "1.2.2")' "$module_file"; then
  echo "MODULE.bazel no longer pins protovalidate v1.2.2" >&2
  exit 1
fi
if ! awk '
  /^[[:space:]]*single_version_override[[:space:]]*\(/ {
    in_override = 1
    matching_module = 0
    matching_version = 0
  }
  in_override && /^[[:space:]]*module_name[[:space:]]*=[[:space:]]*"protovalidate"[[:space:]]*,[[:space:]]*$/ {
    matching_module = 1
  }
  in_override && /^[[:space:]]*version[[:space:]]*=[[:space:]]*"1\.2\.2"[[:space:]]*,[[:space:]]*$/ {
    matching_version = 1
  }
  in_override && /^[[:space:]]*\)[[:space:]]*$/ {
    if (matching_module && matching_version) found = 1
    in_override = 0
  }
  END { exit found ? 0 : 1 }
' "$module_file"; then
  echo "the protovalidate single_version_override no longer pins v1.2.2" >&2
  exit 1
fi

tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT

tail -n +2 "$registry_file" | cut -f1 | LC_ALL=C sort >"$tmp_dir/registered"
: >"$tmp_dir/upstream"
for location_group in "$@"; do
  for source in $location_group; do
    basename "$source" >>"$tmp_dir/upstream"
  done
done
LC_ALL=C sort -u "$tmp_dir/upstream" -o "$tmp_dir/upstream"

if ! diff -u "$tmp_dir/upstream" "$tmp_dir/registered"; then
  echo "the v1.2.2 official case corpus changed without a registry classification" >&2
  exit 1
fi

awk -F '\t' '
  NR == 1 {
    if ($1 != "file" || $2 != "status" || $3 != "coverage" || $4 != "reason") exit 2
    next
  }
  $2 != "supported" && $2 != "rejected" && $2 != "deferred" { exit 3 }
  $3 == "" || $4 == "" { exit 4 }
' "$registry_file" || {
  echo "corpus_registry.tsv contains an invalid or incomplete classification" >&2
  exit 1
}

awk -F '\t' '$2 == "supported" { print $1 }' "$registry_file" |
  LC_ALL=C sort >"$tmp_dir/registered_supported"

# Extract only the srcs block for lean_supported_cases_proto.  Quoted proto
# filenames are intentionally one per line in the patch so this stays strict.
sed -n '/name = "lean_supported_cases_proto"/,/strip_import_prefix/p' "$patch_file" |
  sed -n 's/^+        "\([^"]*\.proto\)",$/\1/p' |
  LC_ALL=C sort >"$tmp_dir/patched_supported"

if ! diff -u "$tmp_dir/registered_supported" "$tmp_dir/patched_supported"; then
  echo "the compiling source target and supported registry have silently diverged" >&2
  exit 1
fi
