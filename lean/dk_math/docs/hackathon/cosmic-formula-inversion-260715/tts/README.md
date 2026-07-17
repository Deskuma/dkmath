# Kokoro TTS environment

The project virtual environment contains `kokoro-tts==2.3.1`, with
`kokoro-onnx==0.3.9` and CPU ONNX Runtime. The host has no available NVIDIA
driver, so this setup uses CPU inference.

The non-versioned model files are stored in `models/`:

```text
models/kokoro-v1.0.onnx
models/voices-v1.0.bin
```

The selected final voice is `af_sarah` in `en-us`. It was accepted in the local
smoke test.

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

## Final narration pipeline

The finalized source is retained in `dkmath-final-narration-tts.txt`; the
English subtitle counterpart is `dkmath-final-narration-en.srt`. The timed
speech cue files under `cues/` use spoken-number and spoken-`G N` forms to
protect pronunciation.

From the repository root, build the narration:

```bash
bash lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/build_final_narration.sh
```

This generates one raw WAV per cue, then creates exact 174-second cue slots.
When a raw cue exceeds its allotted slot it is sped up only by the measured
`raw_duration / slot_duration` factor; otherwise it is left at native speed and
padded with end silence. `loudnorm` then produces a 48 kHz mono master at
`I=-16`, `TP=-1.5`, and `LRA=11`.

Outputs, all excluded from git:

```text
output/raw/cue_01.wav ... cue_11.wav
output/timed/cue_01.wav ... cue_11.wav
output/timing.tsv
output/dkmath-final-narration-timed.wav
output/dkmath-final-narration-normalized.wav
```

Do not use `--stream` in headless production; it requires a working audio
device, whereas file output does not need playback. License and model provenance
are recorded in `LICENSE_PROVENANCE.md`. The final reproducibility report,
including cue timing and output verification, is `FINAL_NARRATION_REPORT.md`.

Official package and model sources:

- https://github.com/nazdridoy/kokoro-tts
- https://github.com/nazdridoy/kokoro-tts/releases/tag/v1.0.0
