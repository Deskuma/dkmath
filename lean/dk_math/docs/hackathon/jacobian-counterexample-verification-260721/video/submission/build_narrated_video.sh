#!/usr/bin/env bash
set -euo pipefail

submission_dir="$(cd "$(dirname "$0")" && pwd)"
video_dir="$submission_dir/.."
audio_builder="$video_dir/tts/build_narration.sh"
visual_builder="$video_dir/visual/build_visual.sh"
visual="$video_dir/visual/output/BreakingMathVerificationVisual.mp4"
audio="$video_dir/tts/output/narration-normalized.wav"
subtitles="$video_dir/tts/narration-en.srt"
output="$submission_dir/output/BreakingMathVerification.mp4"

bash "$audio_builder"
bash "$visual_builder"
mkdir -p "$submission_dir/output"

ffmpeg -nostdin -y -v error \
  -i "$visual" -i "$audio" \
  -filter_complex \
  "[0:v]subtitles='$subtitles':force_style='FontName=DejaVu Sans,FontSize=22,PrimaryColour=&H00FFFFFF,OutlineColour=&H0008111F,BorderStyle=3,Outline=1,Shadow=0,MarginV=18,Alignment=2'[v]" \
  -map "[v]" -map 1:a:0 \
  -c:v libx264 -preset medium -crf 18 -pix_fmt yuv420p -r 30 \
  -c:a aac -b:a 192k -ar 48000 -ac 1 \
  -shortest -movflags +faststart "$output"

printf '%s\n' "$output"
