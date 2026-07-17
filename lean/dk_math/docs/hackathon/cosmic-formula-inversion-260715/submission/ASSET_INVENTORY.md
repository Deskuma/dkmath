# Final asset inventory

## Submission artifacts

| Asset | Role | Status |
|---|---|---|
| `output/DkMathCosmicPromoFinal.mp4` | 2:54 final visual promo | Generated |
| `output/DkMathCosmicPromoFinalNarrated.mp4` | 2:54 final narrated promo | Generated |
| `narration.srt` | Final timed narration/subtitle source | Included |
| `timeline.ass` | Burned-in evidence-card timeline | Included |
| `build_submission.sh` | Reproducible FFmpeg build | Included |
| `build_narrated_promo.sh` | Reproducible Kokoro/FFmpeg narration build | Included |
| `README.md` | Submission text and reproduction guide | Included |

## Verified source evidence

| Repository asset | Evidence used |
|---|---|
| `DkMath/Hackathon/FinitePrimeEscape.lean` | Freshness definition and finite escape theorems |
| `DkMath/Hackathon/CosmicCompletion.lean` | Completed-square identity |
| `DkMath/Hackathon/Demo.lean` | Fixed values, factorization, freshness, completion |
| `report-hack-001.md` through `report-hack-004.md` | Contract, audit, implementation, fixed demo trail |
| `report-hack-008a.md` | Manim render provenance |
| `report-hack-009a.md` | Accepted integration structure and metadata |

## Embedded moving-image asset

```text
../visual/media/videos/cosmic_formula_scene/720p30/
  CosmicFormulaPrototype.mp4
```

This accepted 15.9-second, 1280x720, 30 fps H.264 clip is inserted full-screen
at 01:48. It has no audio stream.

## Accuracy constraints applied

- The finite-escape card explicitly includes `Nat.Prime q`.
- Freshness is relative to the finite set `{2, 3, 5, 7}`.
- Bounded inverse projection is labeled as future research, not a theorem.
- No Collatz theorem or convergence claim appears.
- No invented collaboration recording or terminal output is included.

## Remaining external assets

- Human narration recording
- Optional music and sound design with appropriate licensing
- Optional authentic Codex collaboration and Lean editor recordings
- Hackathon platform metadata and uploaded media URL
