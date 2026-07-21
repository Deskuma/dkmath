#!/usr/bin/env bash
set -euo pipefail

visual_dir="$(cd "$(dirname "$0")" && pwd)"
timing="$visual_dir/../tts/output/timing.tsv"
ass="$visual_dir/timeline.ass"
output="$visual_dir/output/BreakingMathVerificationVisual.mp4"

test -f "$timing"
test -f "$ass"
mkdir -p "$visual_dir/output"
duration="$(awk -F '\t' 'NR > 1 { end=$3 } END { print end }' "$timing")"

ffmpeg -nostdin -y -v error \
  -f lavfi -i "color=c=0x08111F:s=1280x720:r=30:d=$duration" \
  -vf "ass='$ass'" \
  -c:v libx264 -preset medium -crf 18 -pix_fmt yuv420p \
  -r 30 -t "$duration" -movflags +faststart "$output"

printf '%s\n' "$output"
