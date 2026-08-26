#!/usr/bin/env bash
set -euo pipefail

apply_if_needed() {
  local repository="$1"
  local patch_file="$2"
  if git -C "$repository" apply --check "$patch_file" 2>/dev/null; then
    git -C "$repository" apply "$patch_file"
  elif ! git -C "$repository" apply --reverse --check "$patch_file" 2>/dev/null; then
    echo "Cannot apply $patch_file" >&2
    exit 1
  fi
}

project_dir="$(cd "$(dirname "$0")" && pwd)"
apply_if_needed "$project_dir/.lake/packages/verso" "$project_dir/patches/verso-z85.patch"
apply_if_needed "$project_dir/.lake/packages/verso-slides" \
  "$project_dir/patches/verso-slides-module-path.patch"
