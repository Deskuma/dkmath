# Breaking Math Verification Video

This directory contains the reproducible source package for the English
VIDEO-001 demo. The final video is 1280 by 720, 30 fps, H.264 with AAC audio,
burned-in English subtitles, and no music.

## Build

From `lean/dk_math` run:

```text
bash docs/hackathon/jacobian-counterexample-verification-260721/video/submission/build_narrated_video.sh
bash docs/hackathon/jacobian-counterexample-verification-260721/video/submission/validate_video.sh
```

The build uses the repository `venv`, the accepted Kokoro model and voice files
by reference from the Cosmic Formula factory, and system FFmpeg. Generated raw
audio, intermediate visual media, and validation frames are ignored. The final
MP4 is retained as the submission artifact.

## Layout

```text
tts/         narration cues, native-speed Kokoro build, measured timing, SRT
visual/      generated ASS timeline, renderer, and retained Manim configuration
submission/  one-command build, validation script, and final MP4
```

Manim was not available in the project environment during this checkpoint, and
installing it stopped at the missing host Cairo development dependency. The
first-pass visual is therefore rendered reproducibly with FFmpeg and libass.
`visual/manim.cfg` retains the required canvas settings for a future Manim
upgrade without affecting this complete render.

