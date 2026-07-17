#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
manim="$here/../visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4"
output="$here/output/DkMathCosmicPromoDraft01.mp4"

mkdir -p "$here/output"

ffmpeg -y \
  -f lavfi -i "color=c=0x0B1020:s=1280x720:r=30:d=174" \
  -i "$manim" \
  -filter_complex \
  "[0:v]ass='$here/timeline.ass'[cards];\
   [1:v]scale=1280:720,format=yuva420p,\
   fade=t=in:st=0:d=0.4:alpha=1,\
   fade=t=out:st=15.5:d=0.4:alpha=1,\
   setpts=PTS+108/TB[visual];\
   [cards][visual]overlay=0:0:eof_action=pass:enable='between(t,108,124)'[video]" \
  -map "[video]" \
  -c:v libx264 -preset medium -crf 18 -pix_fmt yuv420p \
  -r 30 -t 174 -movflags +faststart \
  "$output"

printf '%s\n' "$output"

