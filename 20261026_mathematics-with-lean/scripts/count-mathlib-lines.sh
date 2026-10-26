#!/bin/bash
# Usage: count-mathlib-lines.sh REPO REF DIR FROM_YYYY-MM TO_YYYY-MM
# For the first of each month, takes the last first-parent commit of REF before that day and counts
# all lines (including blank lines and comments) of the .lean files under DIR.
# Prints "YYYY-MM-01 commit-date lines". Used for scripts/mathlib-lines.txt:
#   count-mathlib-lines.sh path/to/mathlib3 master src 2017-08 2023-10  (prefix each line with "3 ")
#   count-mathlib-lines.sh path/to/mathlib4 master Mathlib 2023-01 2026-10  (prefix with "4 ")
repo=$1 ref=$2 dir=$3 from=$4 to=$5
d="$from-01"
while [[ "$d" < "$(date -d "$to-01 +1 month" +%F)" ]]; do
  c=$(git -C "$repo" rev-list -1 --first-parent --before="$d 00:00" "$ref")
  if [ -n "$c" ]; then
    cd=$(git -C "$repo" log -1 --format=%cs "$c")
    if git -C "$repo" cat-file -e "$c:$dir" 2>/dev/null; then
      n=$(git -C "$repo" archive "$c" "$dir" | tar -xO --wildcards '*.lean' | wc -l)
    else
      # Before January 2019, Mathlib 3 kept its sources at the top level instead of in src/.
      n=$(git -C "$repo" archive "$c" | tar -xO --exclude='tests/*' --exclude='docs/*' \
            --wildcards '*.lean' | wc -l)
    fi
    echo "$d $cd $n"
  fi
  d=$(date -d "$d +1 month" +%F)
done
