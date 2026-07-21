# VIDEO-001 Production Report

## Result

The complete English demo renders successfully at 176.100 seconds. It presents
the reported Jacobian candidate as a case study in an auditable verification
workflow and preserves the boundary between external report, independent DkMath
reconstruction, exact Lean verification, and continuing broader review.

## Discovered Local Factory

- Project environment: `/home/deskuma/develop/lean/dkmath/venv`
- Python: 3.12.3
- Kokoro CLI: 2.3.1 at `venv/bin/kokoro-tts`
- Kokoro runtime package: 0.3.9
- Voice: `af_sarah`, language `en-us`
- Model: accepted `kokoro-v1.0.onnx`, referenced from the Cosmic TTS factory
- Voices: accepted `voices-v1.0.bin`, referenced from the same factory
- FFmpeg and ffprobe: 6.1.1
- Subtitle renderer: FFmpeg libass `subtitles` filter
- Fonts: DejaVu Sans and DejaVu Sans Mono

The accepted Cosmic directories were inspected read-only and were not modified.
No model binary was copied into this project.

## Timing

The first native-speed narration draft measured 228.607 seconds. It was revised
for concision rather than accelerated. The accepted native-speed narration,
including 0.8 seconds of breathing room per cue, measured 176.106 seconds. All
cue `atempo` values remain exactly 1.0. The encoded MP4 measures 176.100 seconds.

The generated `tts/output/timing.tsv` is the source of truth for scene timing.
It drives the ASS visual schedule, sentence-level SRT subtitle schedule, and
final audio duration.

## Rendering Decision

The project venv contained Kokoro but not Manim. Installing Manim reached the
existing package index, then failed while building pycairo because the host did
not provide the Cairo development package. Installing that system dependency
required unavailable sudo authentication. To complete the time-critical video,
the visual layer uses FFmpeg plus libass with measured cards and animated
collision nodes. A valid `manim.cfg` is retained for a later renderer upgrade.

## Mathematical Surface

The video displays the current formal map, determinant minus two, normalization
to determinant one, three pairwise-distinct points with common target
`(1/8, 0, 0)`, and these public declarations:

```text
normalizedJacobianCounterexampleCertificateC
normalized_three_point_collision_C
normalizedCollisionCertificateC_notInjective
DkMath.Verification.CollisionCertificate
```

The audit card reports `propext`, `Classical.choice`, and `Quot.sound` for the
Jacobian certificate and no axioms for the generic collision consequence.

## Validation

```text
video codec: h264
resolution: 1280x720
frame rate: 30/1
audio codec: aac
sample rate: 48000 Hz
channels: 1
duration: 176.100000 seconds
size: 6475208 bytes
sha256: 0ebcc5521e603b3a89b74d5d4c25a0e196a95ea5b952498f9cd0232c79c7981e
```

Eight representative frames were extracted and inspected: cold open,
polynomial map, determinant normalization, collision, Lean audit, AI handoff,
scope boundary, and closing card. Text and subtitles remain inside the 720p
frame and are readable. The collision scene visibly converges three labeled
inputs on the exact common target.

## Public-Safety Review

The narration does not claim discovery by DkMath or acceptance by the broader
community. It contains no GN5, FLT5, Cosmic Formula, finite-prime escape, or
DkMath number-theory narrative. It uses no music or third-party media.

## Outcome

**Outcome A:** a complete, accurate, reproducible, submission-ready video and
source package were produced. The visual implementation records the Manim host
dependency limitation transparently and uses the validated FFmpeg fallback.

