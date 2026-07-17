# Final Kokoro narration report

## Status

The finalized narration is synchronized to the 174-second promo and is under
three minutes. It states the GPT-5.6 and Codex workflow, the verified GN5
result, and the scope boundary: this is **not** a proof of Fermat's Last
Theorem at exponent five.

## Source and voice

- Narration source: `dkmath-final-narration-tts.txt`
- Timed cue source: `cues.tsv` and `cues/01.txt` through `cues/11.txt`
- Subtitle source: `dkmath-final-narration-en.srt` and
  `../submission/narration.srt`
- Voice: `af_sarah`; language: `en-us`
- Runtime: project `venv`, `kokoro-tts==2.3.1`, CPU ONNX Runtime

The eleven cues occupy the complete `[0, 174]` second timeline. Cue 01 was
compressed from 13.162667 to 12 seconds with `atempo=1.096889`. Every other
cue fit its assigned slot at native rate and was end-padded as necessary.

## Audio treatment and verification

The WAV master is 48 kHz mono PCM. FFmpeg normalization uses
`loudnorm=I=-16:TP=-1.5:LRA=11`; the measured final AAC program is
-16.4 LUFS integrated, 5.1 LU LRA, and -1.5 dBFS true peak.

The narrated master was checked as follows:

```text
duration: 174.000000 seconds
video:    H.264, 1280x720, 30 fps
audio:    AAC, 48 kHz, mono
size:     4,658,013 bytes
SHA-256:  e5ebebdcae11a1acd25ab55df8c383dc1a7569b715ac1720c5b4e8adcaf53ff4
```

## Reproduction

From the repository root:

```bash
bash lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/build_final_narration.sh
bash lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/build_narrated_promo.sh
```

The second command is the end-to-end build: it regenerates the visual promo,
synthesizes and normalizes the cue audio, then muxes it with FFmpeg.

## Artifacts

- `output/dkmath-final-narration-normalized.wav` — normalized audio master
  (generated, intentionally ignored by git)
- `output/timing.tsv` — measured source durations and timing adjustments
- `../submission/output/DkMathCosmicPromoFinalNarrated.mp4` — final deliverable
- `LICENSE_PROVENANCE.md` — runtime, model, voice, and license provenance

The GN5 statements correspond to the checked declarations in
`DkMath/Hackathon/FinitePrimeEscapeGN5.lean`; the narration deliberately limits
the conclusion to a verified local obstruction.
