# VIDEO-001 Breaking Math Verification Demo

## Summary

A complete first-pass English demo video and reproducible production package
now live under `video/`. The final public artifact is a 176.100-second 720p
H.264/AAC video with native-speed Kokoro narration and burned-in subtitles.

## Deliverables

- Final MP4: `video/submission/output/BreakingMathVerification.mp4`
- Reproduction guide: `video/README.md`
- Detailed production and validation report: `video/VIDEO_REPORT.md`
- Native narration source: `video/tts/cues/`
- Measured subtitle and visual schedules: `video/tts/narration-en.srt` and
  `video/visual/timeline.json`
- One-command build and validation scripts under `video/submission/`

## Verification

`ffprobe` confirms 1280 by 720, 30 fps, H.264 video, mono AAC at 48 kHz, and
176.100 seconds. Eight frames spanning all narrative sections were inspected.
The MP4 SHA-256 is:

```text
0ebcc5521e603b3a89b74d5d4c25a0e196a95ea5b952498f9cd0232c79c7981e
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

## Outcome

**Outcome A:** complete renderable package and validated final MP4 delivered.

