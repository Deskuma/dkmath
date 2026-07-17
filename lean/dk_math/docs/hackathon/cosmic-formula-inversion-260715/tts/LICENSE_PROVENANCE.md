# TTS license and provenance

## Runtime

- `kokoro-tts==2.3.1`, by nazdridoy: MIT license.
  Source: https://github.com/nazdridoy/kokoro-tts
- `kokoro-onnx==0.3.9` supplies the local ONNX inference runtime used by the
  selected CLI.

## Model and voice data

- `kokoro-v1.0.onnx` and `voices-v1.0.bin` were downloaded from the
  `nazdridoy/kokoro-tts` v1.0.0 release:
  https://github.com/nazdridoy/kokoro-tts/releases/tag/v1.0.0
- The underlying Kokoro-82M model card identifies the model license as
  Apache-2.0:
  https://huggingface.co/hexgrad/Kokoro-82M

The downloaded model and voice data are deliberately excluded from git. Keep
this provenance with any rendered narration and recheck the upstream terms if
the model source or release artifact changes.

