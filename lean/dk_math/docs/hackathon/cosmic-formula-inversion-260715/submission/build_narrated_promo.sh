#!/usr/bin/env bash
set -euo pipefail

submission_dir="$(cd "$(dirname "$0")" && pwd)"
narration_builder="$submission_dir/../tts/build_final_narration.sh"
video_builder="$submission_dir/build_submission.sh"
video="$submission_dir/output/DkMathCosmicPromoFinal.mp4"
audio="$submission_dir/../tts/output/dkmath-final-narration-normalized.wav"
output="$submission_dir/output/DkMathCosmicPromoFinalNarrated.mp4"

bash "$narration_builder"
bash "$video_builder"

ffmpeg -nostdin -y \
  -i "$video" \
  -i "$audio" \
  -map 0:v:0 -map 1:a:0 \
  -c:v copy -c:a aac -b:a 192k \
  -shortest -movflags +faststart \
  "$output"

printf '%s\n' "$output"
