#!/usr/bin/env bash
set -euo pipefail

submission_dir="$(cd "$(dirname "$0")" && pwd)"
video_dir="$submission_dir/.."
audio_builder="$video_dir/tts/build_narration.sh"
visual_builder="$video_dir/visual/build_visual.sh"
visual="$video_dir/visual/output/BreakingMathVerificationVisual.mp4"
audio="$video_dir/tts/output/narration-normalized.wav"
output="$submission_dir/output/BreakingMathVerification.mp4"

bash "$audio_builder"
bash "$visual_builder"
mkdir -p "$submission_dir/output"

ffmpeg -nostdin -y -v error \
  -i "$visual" -i "$audio" \
  -map 0:v:0 -map 1:a:0 \
  -c:v copy \
  -c:a aac -b:a 192k -ar 48000 -ac 1 \
  -shortest -movflags +faststart "$output"

printf '%s\n' "$output"
