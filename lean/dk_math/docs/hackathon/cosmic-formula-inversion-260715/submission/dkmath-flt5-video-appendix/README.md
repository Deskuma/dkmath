# DkMath FLT5 post-video appendix

A 55-second append-only ending for the existing OpenAI Build Week video.
It is designed to begin immediately after the original GN5 ending, including
an original statement that the local GN5 result was not yet an FLT5 proof.
The first new card resolves that statement by saying the proof was completed
after the original video was recorded.

## Intended repository location

Copy this directory to:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/flt5_appendix/
```

The script reuses the existing Kokoro executable, model, voices, and voice
selection, but does not call or modify `tts/build_final_narration.sh`.

## Build

```bash
cd lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/flt5_appendix
bash build_flt5_appendix.sh /absolute/path/to/shortened-base.mp4
```

Optional output path:

```bash
bash build_flt5_appendix.sh shortened-base.mp4 output/final-with-flt5.mp4
```

## Output

```text
output/DkMathCosmicPromoFLT5Final.mp4
```

The script normalizes both parts to 1280x720, 30 fps, H.264, mono AAC 48 kHz,
then concatenates them. Check the printed duration and keep the total below
180 seconds.

## Timeline

- 00:00–00:11 — Post-video breakthrough
- 00:11–00:25 — Golden lift
- 00:25–00:40 — Same invariant, strict descent
- 00:40–00:55 — Final Lean theorem and CI result

## Files

- `slides.ass` — burned-in four-card ending
- `cues.tsv` and `cues/*.txt` — Kokoro narration
- `build_flt5_appendix.sh` — independent append-only pipeline
