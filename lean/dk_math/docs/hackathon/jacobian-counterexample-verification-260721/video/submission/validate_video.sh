#!/usr/bin/env bash
set -euo pipefail

submission_dir="$(cd "$(dirname "$0")" && pwd)"
video_dir="$submission_dir/.."
video="$submission_dir/output/BreakingMathVerification.mp4"
frames="$video_dir/frames"

test -f "$video"
mkdir -p "$frames"
ffprobe -v error -show_entries \
  format=duration,size:stream=index,codec_name,codec_type,width,height,r_frame_rate,sample_rate,channels \
  -of json "$video"

for entry in \
  "cold-open:4" \
  "polynomial:42" \
  "determinant:61" \
  "collision:81" \
  "lean-audit:116" \
  "workflow:135" \
  "scope:153" \
  "closing:169"; do
  name="${entry%%:*}"
  timestamp="${entry##*:}"
  ffmpeg -nostdin -y -v error -ss "$timestamp" -i "$video" \
    -frames:v 1 "$frames/$name.png"
done

sha256sum "$video"
