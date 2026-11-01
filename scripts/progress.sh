#!/usr/bin/env bash
# Build the exercises and report remaining sorries per file.
cd "$(dirname "$0")/.."
out=$(lake build Exercises 2>&1)
if echo "$out" | grep -q "error:"; then
  echo "$out" | grep -A6 "error:"; echo; echo "Build has errors (above)."; exit 1
fi
total=0
for f in Exercises/*.lean; do
  n=$(echo "$out" | grep -c "$f:.*declaration uses .sorry.")
  total=$((total+n)); printf "%-32s %2d left\n" "$f" "$n"
done
echo "Total: $total"
