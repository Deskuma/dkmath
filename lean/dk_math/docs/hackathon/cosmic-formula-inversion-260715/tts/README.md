# Kokoro TTS environment

The project virtual environment contains `kokoro-tts==2.3.1`, with
`kokoro-onnx==0.3.9` and CPU ONNX Runtime. The host has no available NVIDIA
driver, so this setup uses CPU inference.

The non-versioned model files are stored in `models/`:

```text
models/kokoro-v1.0.onnx
models/voices-v1.0.bin
```

Run a smoke test from the repository root:

```bash
mkdir -p lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/output
venv/bin/kokoro-tts \
  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/smoke_test.txt \
  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/output/smoke_test.wav \
  --lang en-us \
  --voice af_sarah \
  --model lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/models/kokoro-v1.0.onnx \
  --voices lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/models/voices-v1.0.bin
```

For the final promo, use `submission/narration.srt` as the narration source.
Convert its timed cues to plain text per cue before synthesis, then align the
rendered WAV/MP3 clips to the existing 174-second video timeline. Do not use
`--stream` in headless production; it requires a working audio device, whereas
file output does not need playback.

Official package and model sources:

- https://github.com/nazdridoy/kokoro-tts
- https://github.com/nazdridoy/kokoro-tts/releases/tag/v1.0.0
