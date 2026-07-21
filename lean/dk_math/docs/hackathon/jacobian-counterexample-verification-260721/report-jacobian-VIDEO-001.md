# VIDEO-001 Breaking Math Verification Demo

## Summary

A complete first-pass English demo video and reproducible production package
now live under `video/`. The final public artifact is a 176.100-second 720p
H.264/AAC video with native-speed Kokoro narration with an optional SRT sidecar.

## Deliverables

- Final MP4: `video/submission/output/BreakingMathVerification.mp4`
- Reproduction guide: `video/README.md`
- Detailed production and validation report: `video/VIDEO_REPORT.md`
- Native narration source: `video/tts/cues/`
- Measured subtitle and visual schedules: `video/tts/narration-en.srt` and
  `video/visual/timeline.json`
- One-command build and validation scripts under `video/submission/`

The package commit is `8ebeb29c`; the final handoff commit is the `HEAD` printed
in the chat response after this report update. Twenty-five files were added:
this report, the video README and production report, 10 cue texts and their
manifest, TTS/visual/submission scripts, generated SRT/ASS/JSON schedules,
Manim configuration, `.gitignore`, and the final MP4.

## Native Cue Timing

```text
cue  start      end        raw        atempo
01     0.000     16.779     15.979     1.000000
02    16.779     36.608     19.029     1.000000
03    36.608     50.805     13.397     1.000000
04    50.805     68.032     16.427     1.000000
05    68.032     83.915     15.083     1.000000
06    83.915    103.424     18.709     1.000000
07   103.424    123.957     19.733     1.000000
08   123.957    141.098     16.341     1.000000
09   141.098    160.927     19.029     1.000000
10   160.927    176.106     14.379     1.000000
```

## Verification

`ffprobe` confirms 1280 by 720, 30 fps, H.264 video, mono AAC at 48 kHz, and
176.100 seconds. Eight frames spanning all narrative sections were inspected.
The MP4 SHA-256 is:

```text
0ebcc5521e603b3a89b74d5d4c25a0e196a95ea5b952498f9cd0232c79c7981e
```

The inspected timestamps were 4, 42, 61, 81, 116, 135, 153, and 169 seconds,
covering the cold open, polynomial, determinant, collision, Lean audit,
workflow, scope, and closing scenes respectively. No clipping, missing cue, or
unintended submission crossover was found.

The render and mux entry points are:

```text
bash docs/hackathon/jacobian-counterexample-verification-260721/video/visual/build_visual.sh
bash docs/hackathon/jacobian-counterexample-verification-260721/video/submission/build_narrated_video.sh
bash docs/hackathon/jacobian-counterexample-verification-260721/video/submission/validate_video.sh
```

## Scope

The story is limited to the Jacobian candidate and the reusable verification
workflow. It explicitly separates the reported formulas, independent DkMath
reconstruction, kernel-checked formal claims, and continuing mathematical
review. No separate number-theory submission narrative appears.

## Environment Note

The project venv supplied Kokoro TTS but lacked Manim. Manim installation was
blocked by the missing host Cairo development dependency and unavailable sudo
authentication. The complete visual was rendered with the installed FFmpeg and
libass stack; the retained Manim configuration documents the intended upgrade
path. The accepted Cosmic production directory remained read-only.

The only optional remaining human action is installing the host Cairo and Pango
development packages, adding Manim to the project venv, and upgrading the visual
renderer later. It is not required to reproduce or submit the delivered MP4.

## Outcome

**Outcome A:** complete renderable package and validated final MP4 delivered.
